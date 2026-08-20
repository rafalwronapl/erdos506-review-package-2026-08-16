import Erdos506.V1.TenFive

/-!
# Bounded arithmetic for the three-pentagon loss table

This module contains only small pointwise tables and their generic finite
sums.  It does not enumerate labelled block systems.  The three possible
five-degree profiles are obtained from the first and second moments, while
the line-loss estimates use a two-unit loss counter.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

/-- Number of points on which `d` has a prescribed value. -/
noncomputable def threePentagonDegreeCount
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (d : Point → Nat) (r : Nat) : Nat :=
  ((Finset.univ : Finset Point).filter fun p => d p = r).card

theorem degree_ne_of_threePentagonDegreeCount_eq_zero
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (d : Point → Nat) {r : Nat}
    (hzero : threePentagonDegreeCount d r = 0) (p : Point) :
    d p ≠ r := by
  classical
  intro hp
  have hmem : p ∈ (Finset.univ : Finset Point).filter
      (fun q => d q = r) := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
  have hpos := Finset.card_pos.mpr ⟨p, hmem⟩
  change 0 < threePentagonDegreeCount d r at hpos
  omega

/-- The low (`d3 = 6`) zero-four-line baseline from the local table. -/
def threePentagonBaseline : Nat → Nat
  | 0 => 4
  | 1 => 3
  | 2 => 2
  | 3 => 3
  | _ => 0

/-- One unit represents two units of loss from the zero-four-line baseline. -/
def threePentagonLossUnits : Nat → Nat → Nat
  | q, 0 => q
  | q, 1 => if q = 0 then 0 else 1
  | q, 2 => q - 1
  | q, 3 => q
  | _, _ => 0

/-- The possible one-unit high-point credit. -/
def threePentagonHighIndicator (d3 : Nat) : Nat :=
  if d3 = 9 then 1 else 0

/-- Three five-blocks on ten points have exactly the three degree profiles
`(1^5,2^5)`, `(1^6,2^3,3)`, and `(0,1^3,2^6)`. -/
theorem threePentagon_fiveDegree_profile
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (hPoint : Fintype.card Point = 10) (d : Point → Nat)
    (hdle : ∀ p, d p ≤ 3)
    (hsum : (∑ p : Point, d p) = 15)
    (hsecond : (∑ p : Point, Nat.choose (d p) 2) ≤ 6) :
    let m := ∑ p : Point, Nat.choose (d p) 2
    let n₀ := threePentagonDegreeCount d 0
    let n₁ := threePentagonDegreeCount d 1
    let n₂ := threePentagonDegreeCount d 2
    let n₃ := threePentagonDegreeCount d 3
    (m = 5 ∧ n₀ = 0 ∧ n₁ = 5 ∧ n₂ = 5 ∧ n₃ = 0) ∨
      (m = 6 ∧ n₀ = 0 ∧ n₁ = 6 ∧ n₂ = 3 ∧ n₃ = 1) ∨
      (m = 6 ∧ n₀ = 1 ∧ n₁ = 3 ∧ n₂ = 6 ∧ n₃ = 0) := by
  classical
  dsimp only
  let m := ∑ p : Point, Nat.choose (d p) 2
  let n₀ := threePentagonDegreeCount d 0
  let n₁ := threePentagonDegreeCount d 1
  let n₂ := threePentagonDegreeCount d 2
  let n₃ := threePentagonDegreeCount d 3
  have hmomentPoint (p : Point) :
      Nat.choose (d p) 2 + 1 =
        d p + (if d p = 0 then 1 else 0) +
          (if d p = 3 then 1 else 0) := by
    have hp := hdle p
    interval_cases hd : d p <;> norm_num [Nat.choose] at *
  have hbalancePoint (p : Point) :
      d p + 2 * (if d p = 0 then 1 else 0) +
          (if d p = 1 then 1 else 0) =
        2 + (if d p = 3 then 1 else 0) := by
    have hp := hdle p
    interval_cases hd : d p <;> norm_num at *
  have hpartitionPoint (p : Point) :
      (if d p = 0 then 1 else 0) +
          (if d p = 1 then 1 else 0) +
          (if d p = 2 then 1 else 0) +
          (if d p = 3 then 1 else 0) = 1 := by
    have hp := hdle p
    interval_cases hd : d p <;> norm_num at *
  have hmomentSum :
      (∑ p : Point, (Nat.choose (d p) 2 + 1)) =
        ∑ p : Point,
          (d p + (if d p = 0 then 1 else 0) +
            (if d p = 3 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hmomentPoint p
  have hbalanceSum :
      (∑ p : Point,
        (d p + 2 * (if d p = 0 then 1 else 0) +
          (if d p = 1 then 1 else 0))) =
        ∑ p : Point, (2 + (if d p = 3 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hbalancePoint p
  have hpartitionSum :
      (∑ p : Point,
        ((if d p = 0 then 1 else 0) +
          (if d p = 1 then 1 else 0) +
          (if d p = 2 then 1 else 0) +
          (if d p = 3 then 1 else 0))) =
        ∑ _p : Point, 1 := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpartitionPoint p
  have hzero : (∑ p : Point, if d p = 0 then 1 else 0) = n₀ := by
    simp [n₀, threePentagonDegreeCount]
  have hone : (∑ p : Point, if d p = 1 then 1 else 0) = n₁ := by
    simp [n₁, threePentagonDegreeCount]
  have htwo : (∑ p : Point, if d p = 2 then 1 else 0) = n₂ := by
    simp [n₂, threePentagonDegreeCount]
  have hthree : (∑ p : Point, if d p = 3 then 1 else 0) = n₃ := by
    simp [n₃, threePentagonDegreeCount]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.mul_one, ← Finset.mul_sum] at hmomentSum hbalanceSum
  rw [hsum, hPoint, hzero, hthree] at hmomentSum
  rw [hsum, hPoint, hzero, hone, hthree] at hbalanceSum
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.mul_one] at hpartitionSum
  rw [hPoint, hzero, hone, htwo, hthree] at hpartitionSum
  change m ≤ 6 at hsecond
  change m + 10 = 15 + n₀ + n₃ at hmomentSum
  change 15 + 2 * n₀ + n₁ = 20 + n₃ at hbalanceSum
  change n₀ + n₁ + n₂ + n₃ = 10 at hpartitionSum
  have hmLower : 5 ≤ m := by omega
  interval_cases hm : m
  · left
    refine ⟨by simpa only [m] using hm, ?_, ?_, ?_, ?_⟩ <;> omega
  · by_cases hn₀ : n₀ = 0
    · right; left
      refine ⟨by simpa only [m] using hm, ?_, ?_, ?_, ?_⟩ <;> omega
    · right; right
      refine ⟨by simpa only [m] using hm, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Sum of the printed low baselines, expressed through the four profile
counts. -/
theorem sum_threePentagonBaseline_eq_counts
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (d : Point → Nat) (hdle : ∀ p, d p ≤ 3) :
    (∑ p : Point, threePentagonBaseline (d p)) =
      4 * threePentagonDegreeCount d 0 +
        3 * threePentagonDegreeCount d 1 +
        2 * threePentagonDegreeCount d 2 +
        3 * threePentagonDegreeCount d 3 := by
  classical
  have hpoint (p : Point) :
      threePentagonBaseline (d p) =
        4 * (if d p = 0 then 1 else 0) +
          3 * (if d p = 1 then 1 else 0) +
          2 * (if d p = 2 then 1 else 0) +
          3 * (if d p = 3 then 1 else 0) := by
    have hp := hdle p
    interval_cases hd : d p <;> norm_num [threePentagonBaseline] at *
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [threePentagonDegreeCount]

/-- The local table loses twice `threePentagonLossUnits`; a high point may
refund at most one unit through the baseline credit. -/
theorem threePentagon_cap_add_loss_le_baseline
    {d3 q r : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hq : q ≤ 2) (hr : r ≤ 3)
    (hallowed : tenLocalStateAllowed d3 q r) :
    tenLocalLine3Cap d3 q r + 2 * threePentagonLossUnits q r ≤
      threePentagonBaseline r + threePentagonHighIndicator d3 := by
  rcases hd3 with rfl | rfl <;>
    interval_cases q <;> interval_cases r <;>
    simp [tenLocalStateAllowed, tenLocalLine3Cap, threePentagonLossUnits,
      threePentagonBaseline, threePentagonHighIndicator] at hallowed ⊢

/-- Generic summed form of the preceding bounded table. -/
theorem sum_threePentagonCap_add_loss_le_baseline
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (d3 q r : Point → Nat)
    (hd3 : ∀ p, d3 p = 6 ∨ d3 p = 9)
    (hq : ∀ p, q p ≤ 2) (hr : ∀ p, r p ≤ 3)
    (hallowed : ∀ p, tenLocalStateAllowed (d3 p) (q p) (r p)) :
    (∑ p : Point, tenLocalLine3Cap (d3 p) (q p) (r p)) +
        2 * (∑ p : Point, threePentagonLossUnits (q p) (r p)) ≤
      (∑ p : Point, threePentagonBaseline (r p)) +
        ∑ p : Point, threePentagonHighIndicator (d3 p) := by
  have hsum := Finset.sum_le_sum (fun p
    (_hp : p ∈ (Finset.univ : Finset Point)) =>
      threePentagon_cap_add_loss_le_baseline
        (hd3 p) (hq p) (hr p) (hallowed p))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum

/-- With at most one four-line through a positive-degree point, the loss
counter plus the weighted five-degree pays for twice its four-line degree. -/
theorem threePentagon_two_q_le_loss_add_qr_of_q_le_one
    {q r : Nat} (hq : q ≤ 1) (hrpos : 1 ≤ r) (hr : r ≤ 3) :
    2 * q ≤ threePentagonLossUnits q r + q * r := by
  interval_cases q <;> interval_cases r <;>
    simp [threePentagonLossUnits] at *

/-- The corresponding weak inequality when degree zero is allowed. -/
theorem threePentagon_two_q_le_two_loss_add_qr
    {q r : Nat} (hq : q ≤ 2) (hr : r ≤ 2) :
    2 * q ≤ 2 * threePentagonLossUnits q r + q * r := by
  interval_cases q <;> interval_cases r <;>
    simp [threePentagonLossUnits]

/-- In profile `P2`, three degree-two points are the only free first
four-line incidences.  Every remaining incidence consumes the loss counter. -/
theorem threePentagon_q_le_degreeTwoIndicator_add_two_loss
    {q r : Nat} (hq : q ≤ 2) (hrpos : 1 ≤ r) (hr : r ≤ 3) :
    q ≤ (if r = 2 then 1 else 0) +
      2 * threePentagonLossUnits q r := by
  interval_cases q <;> interval_cases r <;>
    simp [threePentagonLossUnits] at *

/-- Summed form of the one-four-line loss estimate. -/
theorem sum_threePentagon_two_q_le_loss_add_qr_of_q_le_one
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (q r : Point → Nat) (hq : ∀ p, q p ≤ 1)
    (hrpos : ∀ p, 1 ≤ r p) (hr : ∀ p, r p ≤ 3) :
    2 * (∑ p : Point, q p) ≤
      (∑ p : Point, threePentagonLossUnits (q p) (r p)) +
        ∑ p : Point, q p * r p := by
  calc
    2 * (∑ p : Point, q p) = ∑ p : Point, 2 * q p := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p : Point,
        (threePentagonLossUnits (q p) (r p) + q p * r p) := by
      exact Finset.sum_le_sum fun p _hp =>
        threePentagon_two_q_le_loss_add_qr_of_q_le_one
          (hq p) (hrpos p) (hr p)
    _ = (∑ p : Point, threePentagonLossUnits (q p) (r p)) +
        ∑ p : Point, q p * r p := by
      rw [Finset.sum_add_distrib]

/-- Summed form of the weak two-four-line loss estimate. -/
theorem sum_threePentagon_two_q_le_two_loss_add_qr
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (q r : Point → Nat) (hq : ∀ p, q p ≤ 2)
    (hr : ∀ p, r p ≤ 2) :
    2 * (∑ p : Point, q p) ≤
      2 * (∑ p : Point, threePentagonLossUnits (q p) (r p)) +
        ∑ p : Point, q p * r p := by
  calc
    2 * (∑ p : Point, q p) = ∑ p : Point, 2 * q p := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p : Point,
        (2 * threePentagonLossUnits (q p) (r p) + q p * r p) := by
      exact Finset.sum_le_sum fun p _hp =>
        threePentagon_two_q_le_two_loss_add_qr (hq p) (hr p)
    _ = 2 * (∑ p : Point, threePentagonLossUnits (q p) (r p)) +
        ∑ p : Point, q p * r p := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Summed form of the `P2` degree-two credit estimate. -/
theorem sum_threePentagon_q_le_degreeTwoIndicator_add_two_loss
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (q r : Point → Nat) (hq : ∀ p, q p ≤ 2)
    (hrpos : ∀ p, 1 ≤ r p) (hr : ∀ p, r p ≤ 3) :
    (∑ p : Point, q p) ≤
      (∑ p : Point, if r p = 2 then 1 else 0) +
        2 * (∑ p : Point, threePentagonLossUnits (q p) (r p)) := by
  calc
    (∑ p : Point, q p) ≤ ∑ p : Point,
        ((if r p = 2 then 1 else 0) +
          2 * threePentagonLossUnits (q p) (r p)) := by
      exact Finset.sum_le_sum fun p _hp =>
        threePentagon_q_le_degreeTwoIndicator_add_two_loss
          (hq p) (hrpos p) (hr p)
    _ = (∑ p : Point, if r p = 2 then 1 else 0) +
        2 * (∑ p : Point, threePentagonLossUnits (q p) (r p)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The `h = 3` table admits a single linear certificate. -/
theorem threePentagon_cap_add_degree_add_q_le
    {d3 q r : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hq : q ≤ 3) (hr : r ≤ 3)
    (hallowed : tenLocalStateAllowed d3 q r) :
    tenLocalLine3Cap d3 q r + r + q ≤
      4 + Nat.choose r 2 + threePentagonHighIndicator d3 := by
  rcases hd3 with rfl | rfl <;>
    interval_cases q <;> interval_cases r <;>
    simp [tenLocalStateAllowed, tenLocalLine3Cap,
      threePentagonHighIndicator, Nat.choose] at hallowed ⊢

/-- Equality in the `h = 3` certificate excludes five-degree three. -/
theorem threePentagon_degree_ne_three_of_cap_certificate_eq
    {d3 q r : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hq : q ≤ 3) (hr : r ≤ 3)
    (hallowed : tenLocalStateAllowed d3 q r)
    (heq : tenLocalLine3Cap d3 q r + r + q =
      4 + Nat.choose r 2 + threePentagonHighIndicator d3) :
    r ≠ 3 := by
  rcases hd3 with rfl | rfl <;>
    interval_cases q <;> interval_cases r <;>
    simp [tenLocalStateAllowed, tenLocalLine3Cap,
      threePentagonHighIndicator, Nat.choose] at hallowed heq ⊢

/-- At five-degree zero, equality in the `h = 3` certificate is exactly the
low off-line row. -/
theorem threePentagon_zero_certificate_eq
    {d3 q : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hq : q ≤ 3)
    (hallowed : tenLocalStateAllowed d3 q 0)
    (heq : tenLocalLine3Cap d3 q 0 + q =
      4 + threePentagonHighIndicator d3) :
    d3 = 6 ∧ q = 0 ∧ tenLocalLine3Cap d3 q 0 = 4 := by
  rcases hd3 with rfl | rfl <;> interval_cases q <;>
    simp [tenLocalStateAllowed, tenLocalLine3Cap,
      threePentagonHighIndicator] at hallowed heq ⊢

/-- Summed form of the linear certificate used in the `h = 3` row. -/
theorem sum_threePentagon_cap_add_degree_add_q_le
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (d3 q r : Point → Nat)
    (hd3 : ∀ p, d3 p = 6 ∨ d3 p = 9)
    (hq : ∀ p, q p ≤ 3) (hr : ∀ p, r p ≤ 3)
    (hallowed : ∀ p, tenLocalStateAllowed (d3 p) (q p) (r p)) :
    (∑ p : Point,
        (tenLocalLine3Cap (d3 p) (q p) (r p) + r p + q p)) ≤
      ∑ p : Point,
        (4 + Nat.choose (r p) 2 + threePentagonHighIndicator (d3 p)) := by
  exact Finset.sum_le_sum fun p _hp =>
    threePentagon_cap_add_degree_add_q_le
      (hd3 p) (hq p) (hr p) (hallowed p)

/-- The complete finite loss classification for the three-pentagon row.

Only scalar incidences, the two mixed-moment bound, and the local table enter
this theorem.  Its selected point is the exceptional off-four-line pivot;
the four-block degree is deliberately absent because it belongs to the
separate local pair-row adapter. -/
theorem threePentagon_exceptional_local_cell
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (hcard : Fintype.card Point = 10) (h : Nat)
    (hhpos : 1 ≤ h) (hhle : h ≤ 3)
    (d3 q r l3 : Point → Nat)
    (hd3 : ∀ p, d3 p = 6 ∨ d3 p = 9)
    (hq : ∀ p, q p ≤ h) (hr : ∀ p, r p ≤ 3)
    (hallowed : ∀ p, tenLocalStateAllowed (d3 p) (q p) (r p))
    (hl3cap : ∀ p, l3 p ≤ tenLocalLine3Cap (d3 p) (q p) (r p))
    (hrsum : (∑ p : Point, r p) = 15)
    (hsecond : (∑ p : Point, Nat.choose (r p) 2) ≤ 6)
    (hqsum : (∑ p : Point, q p) = 4 * h)
    (hcross : (∑ p : Point, q p * r p) ≤ 6 * h)
    (hl3sum : (∑ p : Point, l3 p) = 3 * (10 - h))
    (hhighsum :
      (∑ p : Point, threePentagonHighIndicator (d3 p)) = 2) :
    ∃ p : Point,
      d3 p = 6 ∧ r p = 0 ∧ q p = 0 ∧ l3 p = 4 := by
  classical
  have hprofile := threePentagon_fiveDegree_profile
    hcard r hr hrsum hsecond
  have hcapLower :
      (∑ p : Point, l3 p) ≤
        ∑ p : Point, tenLocalLine3Cap (d3 p) (q p) (r p) :=
    Finset.sum_le_sum fun p _hp => hl3cap p
  have hbase := sum_threePentagonBaseline_eq_counts r hr
  interval_cases h
  · have hcapLoss := sum_threePentagonCap_add_loss_le_baseline
      d3 q r hd3 (fun p => by have hp := hq p; omega) hr hallowed
    rcases hprofile with
      ⟨_hm, hn₀, hn₁, hn₂, hn₃⟩ |
      ⟨_hm, hn₀, hn₁, hn₂, hn₃⟩ |
      ⟨_hm, hn₀, hn₁, hn₂, hn₃⟩
    · have hrpos (p : Point) : 1 ≤ r p := by
        have hne := degree_ne_of_threePentagonDegreeCount_eq_zero
          r hn₀ p
        omega
      have hloss :=
        sum_threePentagon_two_q_le_loss_add_qr_of_q_le_one q r
          (fun p => by simpa using hq p) hrpos hr
      rw [hqsum] at hloss
      have hbaseP := hbase
      rw [hn₀, hn₁, hn₂, hn₃] at hbaseP
      norm_num at hbaseP
      rw [hbaseP, hhighsum] at hcapLoss
      rw [hl3sum] at hcapLower
      norm_num at hcapLower hloss hcross
      omega
    · have hrpos (p : Point) : 1 ≤ r p := by
        have hne := degree_ne_of_threePentagonDegreeCount_eq_zero
          r hn₀ p
        omega
      have hloss :=
        sum_threePentagon_two_q_le_loss_add_qr_of_q_le_one q r
          (fun p => by simpa using hq p) hrpos hr
      rw [hqsum] at hloss
      have hbaseP := hbase
      rw [hn₀, hn₁, hn₂, hn₃] at hbaseP
      norm_num at hbaseP
      rw [hbaseP, hhighsum] at hcapLoss
      rw [hl3sum] at hcapLower
      norm_num at hcapLower hloss hcross
      omega
    · have hrleTwo (p : Point) : r p ≤ 2 := by
        have hne := degree_ne_of_threePentagonDegreeCount_eq_zero
          r hn₃ p
        have hp := hr p
        omega
      have hloss := sum_threePentagon_two_q_le_two_loss_add_qr q r
        (fun p => by have hp := hq p; omega) hrleTwo
      rw [hqsum] at hloss
      have hbaseP := hbase
      rw [hn₀, hn₁, hn₂, hn₃] at hbaseP
      norm_num at hbaseP
      rw [hbaseP, hhighsum] at hcapLoss
      rw [hl3sum] at hcapLower
      norm_num at hcapLower hloss hcross
      omega
  · have hcapLoss := sum_threePentagonCap_add_loss_le_baseline
      d3 q r hd3 (fun p => by simpa using hq p) hr hallowed
    rcases hprofile with
      ⟨_hm, hn₀, hn₁, hn₂, hn₃⟩ |
      ⟨_hm, hn₀, hn₁, hn₂, hn₃⟩ |
      ⟨_hm, hn₀, hn₁, hn₂, hn₃⟩
    · have hrleTwo (p : Point) : r p ≤ 2 := by
        have hne := degree_ne_of_threePentagonDegreeCount_eq_zero
          r hn₃ p
        have hp := hr p
        omega
      have hloss := sum_threePentagon_two_q_le_two_loss_add_qr q r
        (fun p => by simpa using hq p) hrleTwo
      rw [hqsum] at hloss
      have hbaseP := hbase
      rw [hn₀, hn₁, hn₂, hn₃] at hbaseP
      norm_num at hbaseP
      rw [hbaseP, hhighsum] at hcapLoss
      rw [hl3sum] at hcapLower
      norm_num at hcapLower hloss hcross
      omega
    · have hrpos (p : Point) : 1 ≤ r p := by
        have hne := degree_ne_of_threePentagonDegreeCount_eq_zero
          r hn₀ p
        omega
      have hloss :=
        sum_threePentagon_q_le_degreeTwoIndicator_add_two_loss q r
          (fun p => by simpa using hq p) hrpos hr
      have htwo :
          (∑ p : Point, if r p = 2 then 1 else 0) =
            threePentagonDegreeCount r 2 := by
        simp [threePentagonDegreeCount]
      rw [hqsum, htwo, hn₂] at hloss
      have hbaseP := hbase
      rw [hn₀, hn₁, hn₂, hn₃] at hbaseP
      norm_num at hbaseP
      rw [hbaseP, hhighsum] at hcapLoss
      rw [hl3sum] at hcapLower
      norm_num at hcapLower hloss
      omega
    · have hrleTwo (p : Point) : r p ≤ 2 := by
        have hne := degree_ne_of_threePentagonDegreeCount_eq_zero
          r hn₃ p
        have hp := hr p
        omega
      have hloss := sum_threePentagon_two_q_le_two_loss_add_qr q r
        (fun p => by simpa using hq p) hrleTwo
      rw [hqsum] at hloss
      have hbaseP := hbase
      rw [hn₀, hn₁, hn₂, hn₃] at hbaseP
      norm_num at hbaseP
      rw [hbaseP, hhighsum] at hcapLoss
      rw [hl3sum] at hcapLower
      norm_num at hcapLower hloss hcross
      omega
  · have hqThree (p : Point) : q p ≤ 3 := by
      simpa using hq p
    have hcert := sum_threePentagon_cap_add_degree_add_q_le
      d3 q r hd3 hqThree hr hallowed
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at hcert
    rw [hcard, hrsum, hqsum, hhighsum] at hcert
    rw [hl3sum] at hcapLower
    norm_num at hcert hcapLower
    have hcapEq :
        (∑ p : Point, tenLocalLine3Cap (d3 p) (q p) (r p)) = 21 := by
      omega
    have hsecondEq :
        (∑ p : Point, Nat.choose (r p) 2) = 6 := by
      omega
    have hcertPointLe (p : Point) :
        tenLocalLine3Cap (d3 p) (q p) (r p) + r p + q p ≤
          4 + Nat.choose (r p) 2 +
            threePentagonHighIndicator (d3 p) :=
      threePentagon_cap_add_degree_add_q_le
        (hd3 p) (hqThree p) (hr p) (hallowed p)
    have hcertEq :
        (∑ p : Point,
            (tenLocalLine3Cap (d3 p) (q p) (r p) + r p + q p)) =
          ∑ p : Point,
            (4 + Nat.choose (r p) 2 +
              threePentagonHighIndicator (d3 p)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      rw [hcapEq, hrsum, hqsum, hcard, hsecondEq, hhighsum]
      norm_num
    have hcertPoint (p : Point) :
        tenLocalLine3Cap (d3 p) (q p) (r p) + r p + q p =
          4 + Nat.choose (r p) 2 +
            threePentagonHighIndicator (d3 p) :=
      (Finset.sum_eq_sum_iff_of_le
        (fun x (_hx : x ∈ (Finset.univ : Finset Point)) =>
          hcertPointLe x)).mp hcertEq p (Finset.mem_univ p)
    have hrneThree (p : Point) : r p ≠ 3 :=
      threePentagon_degree_ne_three_of_cap_certificate_eq
        (hd3 p) (hqThree p) (hr p) (hallowed p) (hcertPoint p)
    have hzero : ∃ p : Point, r p = 0 := by
      by_contra hnone
      have hchoosePoint (p : Point) : Nat.choose (r p) 2 + 1 = r p := by
        have hrzero : r p ≠ 0 := by
          intro hp
          exact hnone ⟨p, hp⟩
        have hrthree := hrneThree p
        have hrange := hr p
        have hroneTwo : r p = 1 ∨ r p = 2 := by omega
        rcases hroneTwo with hp | hp
        · simp [hp]
        · simp [hp]
      have hchooseSum :
          (∑ p : Point, (Nat.choose (r p) 2 + 1)) =
            ∑ p : Point, r p := by
        exact Finset.sum_congr rfl fun p _hp => hchoosePoint p
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, Nat.mul_one] at hchooseSum
      rw [hsecondEq, hcard, hrsum] at hchooseSum
      norm_num at hchooseSum
    obtain ⟨p, hpzero⟩ := hzero
    have hzeroEq :
        tenLocalLine3Cap (d3 p) (q p) 0 + q p =
          4 + threePentagonHighIndicator (d3 p) := by
      simpa [hpzero, Nat.choose] using hcertPoint p
    obtain ⟨hd3p, hqp, hcapp⟩ := threePentagon_zero_certificate_eq
      (hd3 p) (hqThree p) (by simpa [hpzero] using hallowed p) hzeroEq
    have hl3sumEq :
        (∑ x : Point, l3 x) =
          ∑ x : Point, tenLocalLine3Cap (d3 x) (q x) (r x) := by
      rw [hl3sum, hcapEq]
    have hl3p := (Finset.sum_eq_sum_iff_of_le
      (fun x (_hx : x ∈ (Finset.univ : Finset Point)) => hl3cap x)).mp
        hl3sumEq p (Finset.mem_univ p)
    refine ⟨p, hd3p, hpzero, hqp, ?_⟩
    rw [hl3p, hpzero, hqp]
    simpa [hqp] using hcapp

end Erdos506.V1
