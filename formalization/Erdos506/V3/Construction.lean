import Erdos506.V3.NearCircle
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Explicit generic V3 construction

The base points use the rational parametrisation
`((1-t²)/(1+t²), 2t/(1+t²))` with positive, distinct parameters below one.
The outsider is the centre of the unit circle.  All base points lie in one
open semicircle, so no line through the centre contains two of them.
-/

namespace Erdos506.V3

open Erdos506.V4

/-- Labels for `n-1` base-circle points and one outsider. -/
abbrev NearCircleLabels (n : ℕ) := Fin (n - 1) ⊕ Unit

noncomputable def rationalCirclePoint (t : ℝ) : Point2 :=
  EuclideanSpace.single (0 : Fin 2) ((1 - t^2) / (1 + t^2)) +
    EuclideanSpace.single (1 : Fin 2) (2 * t / (1 + t^2))

@[simp] theorem rationalCirclePoint_apply_zero (t : ℝ) :
    rationalCirclePoint t (0 : Fin 2) = (1 - t^2) / (1 + t^2) := by
  simp [rationalCirclePoint]

@[simp] theorem rationalCirclePoint_apply_one (t : ℝ) :
    rationalCirclePoint t (1 : Fin 2) = 2 * t / (1 + t^2) := by
  simp [rationalCirclePoint]

theorem rationalCirclePoint_norm_sq (t : ℝ) :
    ‖rationalCirclePoint t‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [rationalCirclePoint, Fin.sum_univ_two]
  have hden : 1 + t^2 ≠ 0 := by positivity
  field_simp
  ring

theorem rationalCirclePoint_dist_zero (t : ℝ) :
    dist (rationalCirclePoint t) 0 = 1 := by
  rw [dist_zero_right]
  nlinarith [rationalCirclePoint_norm_sq t,
    norm_nonneg (rationalCirclePoint t)]

theorem rationalCirclePoint_injective_nonneg {t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (h : rationalCirclePoint t = rationalCirclePoint u) : t = u := by
  have hx := congrArg (fun p : Point2 => p (0 : Fin 2)) h
  simp at hx
  have htden : 1 + t^2 ≠ 0 := by positivity
  have huden : 1 + u^2 ≠ 0 := by positivity
  field_simp [htden, huden] at hx
  nlinarith

noncomputable def nearCircleParameter (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  (i.1 + 1 : ℕ) / (n : ℝ)

theorem nearCircleParameter_pos (n : ℕ) (hn : 1 ≤ n) (i : Fin (n - 1)) :
    0 < nearCircleParameter n i := by
  unfold nearCircleParameter
  apply div_pos
  · exact_mod_cast Nat.succ_pos i.1
  · exact_mod_cast (show 0 < n by omega)

theorem nearCircleParameter_lt_one (n : ℕ) (hn : 2 ≤ n)
    (i : Fin (n - 1)) : nearCircleParameter n i < 1 := by
  unfold nearCircleParameter
  rw [div_lt_one (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)]
  exact_mod_cast (show i.1 + 1 < n by omega)

theorem nearCircleParameter_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (nearCircleParameter n) := by
  intro i j hij
  unfold nearCircleParameter at hij
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0] at hij
  apply Fin.ext
  have hijNat : i.1 + 1 = j.1 + 1 := by exact_mod_cast hij
  omega

noncomputable def nearCirclePoint (n : ℕ) : NearCircleLabels n → Point2
  | Sum.inl i => rationalCirclePoint (nearCircleParameter n i)
  | Sum.inr _ => 0

theorem nearCirclePoint_injective (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (nearCirclePoint n) := by
  intro x y hxy
  rcases x with i | u <;> rcases y with j | v
  · have ht : 0 ≤ nearCircleParameter n i :=
      (nearCircleParameter_pos n (by omega) i).le
    have hu : 0 ≤ nearCircleParameter n j :=
      (nearCircleParameter_pos n (by omega) j).le
    have hij := rationalCirclePoint_injective_nonneg ht hu hxy
    exact congrArg Sum.inl (nearCircleParameter_injective n (by omega) hij)
  · have hcoord := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
    have ht := nearCircleParameter_pos n (by omega) i
    simp [nearCirclePoint] at hcoord
    have hden : 0 < 1 + nearCircleParameter n i ^ 2 := by positivity
    rcases hcoord with hzero | hzero <;> nlinarith
  · have hcoord := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
    have ht := nearCircleParameter_pos n (by omega) j
    simp [nearCirclePoint] at hcoord
    have hden : 0 < 1 + nearCircleParameter n j ^ 2 := by positivity
    field_simp [ne_of_gt hden] at hcoord
    nlinarith
  · cases u
    cases v
    rfl

noncomputable def nearCircleConfiguration (n : ℕ) (hn : 4 ≤ n) :
    Configuration (NearCircleLabels n) :=
  ⟨nearCirclePoint n, nearCirclePoint_injective n hn⟩

noncomputable def baseSphere : EuclideanGeometry.Sphere Point2 := ⟨0, 1⟩

noncomputable def baseProperCircle : ProperCircle :=
  ⟨baseSphere, by norm_num [baseSphere]⟩

theorem rationalCirclePoint_mem_baseSphere (t : ℝ) :
    rationalCirclePoint t ∈ baseSphere := by
  rw [EuclideanGeometry.mem_sphere]
  exact rationalCirclePoint_dist_zero t

theorem zero_not_mem_baseSphere : (0 : Point2) ∉ baseSphere := by
  rw [EuclideanGeometry.mem_sphere]
  norm_num [baseSphere]

/-- Three distinct points on one positive-radius Euclidean sphere are not
collinear. -/
theorem not_collinear_three_distinct_on_sphere
    {s : EuclideanGeometry.Sphere Point2} {p q r : Point2}
    (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬Collinear ℝ ({p, q, r} : Set Point2) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hpqr | hqrp | hrpq
  · have hs : Sbtw ℝ p q r := ⟨hpqr, hpq.symm, hqr⟩
    have hlt := s.dist_center_lt_radius_of_sbtw hp hr hs
    have heq := EuclideanGeometry.mem_sphere'.mp hq
    linarith
  · have hs : Sbtw ℝ q r p := ⟨hqrp, hqr.symm, hpr.symm⟩
    have hlt := s.dist_center_lt_radius_of_sbtw hq hp hs
    have heq := EuclideanGeometry.mem_sphere'.mp hr
    linarith
  · have hs : Sbtw ℝ r p q := ⟨hrpq, hpr, hpq⟩
    have hlt := s.dist_center_lt_radius_of_sbtw hr hq hs
    have heq := EuclideanGeometry.mem_sphere'.mp hp
    linarith

/-- The centre and two distinct positive-parameter base points are not
collinear. -/
theorem not_collinear_zero_rationalCirclePoints {t u : ℝ}
    (ht : 0 < t) (hu : 0 < u) (htu : t ≠ u) :
    ¬Collinear ℝ
      ({(0 : Point2), rationalCirclePoint t, rationalCirclePoint u} : Set Point2) := by
  intro hcol
  rw [collinear_iff_of_mem (show (0 : Point2) ∈
      ({(0 : Point2), rationalCirclePoint t, rationalCirclePoint u} : Set Point2) by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨a, ha⟩ := hv (rationalCirclePoint t) (by simp)
  obtain ⟨b, hb⟩ := hv (rationalCirclePoint u) (by simp)
  have hzero :
      rationalCirclePoint t 0 * rationalCirclePoint u 1 -
          rationalCirclePoint t 1 * rationalCirclePoint u 0 = 0 := by
    rw [ha, hb]
    simp
    ring
  have htden : 1 + t^2 ≠ 0 := by positivity
  have huden : 1 + u^2 ≠ 0 := by positivity
  have hformula :
      rationalCirclePoint t 0 * rationalCirclePoint u 1 -
          rationalCirclePoint t 1 * rationalCirclePoint u 0 =
        2 * (u - t) * (1 + t * u) / ((1 + t^2) * (1 + u^2)) := by
    simp
    field_simp
    ring
  have hdiff : u - t ≠ 0 := sub_ne_zero.mpr htu.symm
  have hplus : 1 + t * u ≠ 0 := by positivity
  have hnonzero :
      2 * (u - t) * (1 + t * u) / ((1 + t^2) * (1 + u^2)) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) hdiff) hplus
    · exact mul_ne_zero htden huden
  exact hnonzero (hformula ▸ hzero)

theorem nearCirclePoint_three_noncollinear (n : ℕ) (hn : 4 ≤ n)
    {a b c : NearCircleLabels n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬Collinear ℝ
      ({nearCirclePoint n a, nearCirclePoint n b, nearCirclePoint n c} : Set Point2) := by
  rcases a with i | u <;> rcases b with j | v <;> rcases c with k | w
  · apply not_collinear_three_distinct_on_sphere
      (rationalCirclePoint_mem_baseSphere _)
      (rationalCirclePoint_mem_baseSphere _)
      (rationalCirclePoint_mem_baseSphere _)
    · exact fun h => hab (congrArg Sum.inl
        (nearCircleParameter_injective n (by omega)
          (rationalCirclePoint_injective_nonneg
            (nearCircleParameter_pos n (by omega) i).le
            (nearCircleParameter_pos n (by omega) j).le h)))
    · exact fun h => hac (congrArg Sum.inl
        (nearCircleParameter_injective n (by omega)
          (rationalCirclePoint_injective_nonneg
            (nearCircleParameter_pos n (by omega) i).le
            (nearCircleParameter_pos n (by omega) k).le h)))
    · exact fun h => hbc (congrArg Sum.inl
        (nearCircleParameter_injective n (by omega)
          (rationalCirclePoint_injective_nonneg
            (nearCircleParameter_pos n (by omega) j).le
            (nearCircleParameter_pos n (by omega) k).le h)))
  · have h := not_collinear_zero_rationalCirclePoints
      (nearCircleParameter_pos n (by omega) i)
      (nearCircleParameter_pos n (by omega) j)
      (fun hij => hab (congrArg Sum.inl
        (nearCircleParameter_injective n (by omega) hij)))
    have hset :
        ({rationalCirclePoint (nearCircleParameter n i),
          rationalCirclePoint (nearCircleParameter n j), (0 : Point2)} : Set Point2) =
        ({(0 : Point2), rationalCirclePoint (nearCircleParameter n i),
          rationalCirclePoint (nearCircleParameter n j)} : Set Point2) := by
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    simpa only [nearCirclePoint, hset] using h
  · have h := not_collinear_zero_rationalCirclePoints
      (nearCircleParameter_pos n (by omega) i)
      (nearCircleParameter_pos n (by omega) k)
      (fun hik => hac (congrArg Sum.inl
        (nearCircleParameter_injective n (by omega) hik)))
    have hset :
        ({rationalCirclePoint (nearCircleParameter n i), (0 : Point2),
          rationalCirclePoint (nearCircleParameter n k)} : Set Point2) =
        ({(0 : Point2), rationalCirclePoint (nearCircleParameter n i),
          rationalCirclePoint (nearCircleParameter n k)} : Set Point2) := by
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    simpa only [nearCirclePoint, hset] using h
  · cases v
    cases w
    exact False.elim (hbc rfl)
  · have h := not_collinear_zero_rationalCirclePoints
      (nearCircleParameter_pos n (by omega) j)
      (nearCircleParameter_pos n (by omega) k)
      (fun hjk => hbc (congrArg Sum.inl
        (nearCircleParameter_injective n (by omega) hjk)))
    simpa only [nearCirclePoint] using h
  · cases u
    cases w
    exact False.elim (hac rfl)
  · cases u
    cases v
    exact False.elim (hab rfl)
  · cases u
    cases v
    exact False.elim (hab rfl)

theorem nearCircleConfiguration_noThree (n : ℕ) (hn : 4 ≤ n) :
    NoThreeCollinear (nearCircleConfiguration n hn) := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht
  have hsupp : supportPoints (nearCircleConfiguration n hn) ({a, b, c} :
      Finset (NearCircleLabels n)) =
      ({nearCirclePoint n a, nearCirclePoint n b,
        nearCirclePoint n c} : Set Point2) := by
    ext p
    simp [supportPoints, nearCircleConfiguration, eq_comm]
  rw [IsNoncollinear, hsupp]
  exact nearCirclePoint_three_noncollinear n hn hab hac hbc

theorem card_nearCircleLabels (n : ℕ) (hn : 4 ≤ n) :
    Fintype.card (NearCircleLabels n) = n := by
  simp [NearCircleLabels]
  omega

theorem baseLabel_mem_baseCircleTrace (n : ℕ) (hn : 4 ≤ n)
    (i : Fin (n - 1)) :
    Sum.inl i ∈ circleTrace (nearCircleConfiguration n hn) baseProperCircle := by
  rw [mem_circleTrace]
  exact rationalCirclePoint_mem_baseSphere _

theorem outsider_not_mem_baseCircleTrace (n : ℕ) (hn : 4 ≤ n) :
    Sum.inr () ∉ circleTrace (nearCircleConfiguration n hn) baseProperCircle := by
  rw [mem_circleTrace]
  exact zero_not_mem_baseSphere

noncomputable def constructionBaseTriple (n : ℕ) (hn : 4 ≤ n) :
    NoncollinearTriple (nearCircleConfiguration n hn) := by
  let a : NearCircleLabels n := Sum.inl ⟨0, by omega⟩
  let b : NearCircleLabels n := Sum.inl ⟨1, by omega⟩
  let c : NearCircleLabels n := Sum.inl ⟨2, by omega⟩
  refine ⟨{a, b, c}, mem_noncollinearTriples.mpr ⟨?_, ?_⟩⟩
  · simp [a, b, c]
  · exact nearCircleConfiguration_noThree n hn _ (by simp [a, b, c])

theorem baseProperCircle_mem_determinedCircles (n : ℕ) (hn : 4 ≤ n) :
    baseProperCircle ∈ determinedCircles (nearCircleConfiguration n hn) := by
  rw [mem_determinedCircles_iff]
  refine ⟨constructionBaseTriple n hn, ?_⟩
  intro x hx
  change x ∈ ({Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, by omega⟩,
    Sum.inl ⟨2, by omega⟩} : Finset (NearCircleLabels n)) at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    exact rationalCirclePoint_mem_baseSphere _

noncomputable def constructionBaseCircle (n : ℕ) (hn : 4 ≤ n) :
    DeterminedCircle (nearCircleConfiguration n hn) :=
  ⟨baseProperCircle, baseProperCircle_mem_determinedCircles n hn⟩

theorem constructionBaseCircle_trace_card (n : ℕ) (hn : 4 ≤ n) :
    (circleTrace (nearCircleConfiguration n hn)
      (constructionBaseCircle n hn).1).card =
        Fintype.card (NearCircleLabels n) - 1 := by
  have hout : outsiderLabels (nearCircleConfiguration n hn)
      (constructionBaseCircle n hn) = {Sum.inr ()} := by
    classical
    ext x
    rcases x with i | u
    · simp [mem_outsiderLabels, constructionBaseCircle,
        baseLabel_mem_baseCircleTrace n hn i]
    · cases u
      simp [mem_outsiderLabels, constructionBaseCircle,
        outsider_not_mem_baseCircleTrace n hn]
  have hcard := card_outsiderLabels (nearCircleConfiguration n hn)
    (constructionBaseCircle n hn)
  rw [hout] at hcard
  simp only [Finset.card_singleton] at hcard
  have hbasele :
      (circleTrace (nearCircleConfiguration n hn)
        (constructionBaseCircle n hn).1).card ≤
          Fintype.card (NearCircleLabels n) := by
    simpa using Finset.card_le_card
      (show circleTrace (nearCircleConfiguration n hn)
        (constructionBaseCircle n hn).1 ⊆ Finset.univ from Finset.subset_univ _)
  omega

theorem nearCircleConfiguration_notConcyclic (n : ℕ) (hn : 4 ≤ n) :
    NotConcyclic (nearCircleConfiguration n hn) := by
  intro c
  have hle : (circleTrace (nearCircleConfiguration n hn) c).card ≤
      Fintype.card (NearCircleLabels n) := by
    simpa using Finset.card_le_card
      (show circleTrace (nearCircleConfiguration n hn) c ⊆ Finset.univ from
        Finset.subset_univ _)
  apply lt_of_le_of_ne hle
  intro heq
  have hall : circleTrace (nearCircleConfiguration n hn) c = Finset.univ :=
    Finset.eq_univ_of_card _ heq
  let t := constructionBaseTriple n hn
  have ht : ∀ x ∈ t.1,
      nearCircleConfiguration n hn x ∈ (c : Set Point2) := by
    intro x hx
    exact mem_circleTrace.mp (hall.symm ▸ Finset.mem_univ x)
  have hc : c = properCircumcircle (nearCircleConfiguration n hn) t :=
    properCircle_eq_properCircumcircle_of_support
      (nearCircleConfiguration n hn) t c ht
  have hbase : baseProperCircle =
      properCircumcircle (nearCircleConfiguration n hn) t := by
    apply properCircle_eq_properCircumcircle_of_support
    intro x hx
    have : x = Sum.inl ⟨0, by omega⟩ ∨
        x = Sum.inl ⟨1, by omega⟩ ∨ x = Sum.inl ⟨2, by omega⟩ := by
      simpa [t, constructionBaseTriple] using hx
    rcases this with rfl | rfl | rfl <;>
      exact rationalCirclePoint_mem_baseSphere _
  have hcb : c = baseProperCircle := hc.trans hbase.symm
  have houtc : Sum.inr () ∈ circleTrace (nearCircleConfiguration n hn) c := by
    rw [hall]
    simp
  rw [hcb] at houtc
  exact outsider_not_mem_baseCircleTrace n hn houtc

theorem nearCircleConfiguration_admissible (n : ℕ) (hn : 4 ≤ n) :
    Admissible (nearCircleConfiguration n hn) :=
  ⟨nearCircleConfiguration_noThree n hn,
    nearCircleConfiguration_notConcyclic n hn⟩

theorem nearCircleConfiguration_circleCount (n : ℕ) (hn : 4 ≤ n) :
    circleCount (nearCircleConfiguration n hn) = Erdos506.v3GenericTarget n := by
  have hcount := circleCount_eq_generic_of_nearCircle
    (nearCircleConfiguration n hn) (nearCircleConfiguration_noThree n hn)
    (constructionBaseCircle n hn) (constructionBaseCircle_trace_card n hn)
    (by simpa [card_nearCircleLabels n hn] using hn)
  simpa [card_nearCircleLabels n hn] using hcount

/-- Explicit attainment of the generic V3 value for every `n ≥ 4`. -/
theorem exists_generic_extremal_configuration (n : ℕ) (hn : 4 ≤ n) :
    ∃ cfg : Configuration (NearCircleLabels n),
      Fintype.card (NearCircleLabels n) = n ∧ Admissible cfg ∧
        circleCount cfg = Erdos506.v3GenericTarget n := by
  exact ⟨nearCircleConfiguration n hn, card_nearCircleLabels n hn,
    nearCircleConfiguration_admissible n hn,
    nearCircleConfiguration_circleCount n hn⟩

end Erdos506.V3
