import Erdos506.Finite.SixFourIncidenceMoments

/-!
# The external-point entrance for a saturated six-four family

This module extracts the two degree-three points and their three incident
four-subsets from the exact `6`-by-`4` moment profile.  It is the lossless
finite entrance to the subsequent `3 x 3` relabelling argument: no affine or
projective datum is postulated here.
-/

namespace Erdos506.Finite

open scoped BigOperators

universe u

/-- Indices of bases containing a selected point. -/
noncomputable def sixFourBasesThrough {Point : Type*} [DecidableEq Point]
    (B : Fin 6 -> Finset Point) (x : Point) : Finset (Fin 6) :=
  (Finset.univ : Finset (Fin 6)).filter fun i => x ∈ B i

/-- The definition of the six-four degree is exactly the cardinality of its
base fibre. -/
theorem sixFourBasesThrough_card
    {Point : Type*} [DecidableEq Point]
    (B : Fin 6 -> Finset Point) (x : Point) :
    (sixFourBasesThrough B x).card = sixFourDegree B x := rfl

@[simp] theorem mem_sixFourBasesThrough
    {Point : Type*} [DecidableEq Point]
    {B : Fin 6 -> Finset Point} {x : Point} {i : Fin 6} :
    i ∈ sixFourBasesThrough B x ↔ x ∈ B i := by
  simp [sixFourBasesThrough]

/-- A finite saturation contains a canonically enumerable pair of degree-three
points.  The equivalence is deliberately retained, rather than making an
unnamed pair choice. -/
noncomputable def sixFourDegreeThreeEquiv
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    Fin 2 ≃ ↥(sixFourDegreeThree B) := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  simpa only [Fintype.card_coe] using (sixFour_degree_profile H).1

/-- The two distinguished external points, indexed without any geometric
normalization. -/
noncomputable def sixFourExternalPoint
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) : Fin 2 -> Point :=
  fun i => (sixFourDegreeThreeEquiv H i).1

/-- Each extracted external point has degree three. -/
theorem sixFourExternalPoint_degree_eq_three
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (i : Fin 2) :
    sixFourDegree B (sixFourExternalPoint H i) = 3 := by
  change sixFourDegree B ((sixFourDegreeThreeEquiv H i).1) = 3
  exact (Finset.mem_filter.mp (sixFourDegreeThreeEquiv H i).2).2

/-- The two external points are distinct. -/
theorem sixFourExternalPoint_injective
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    Function.Injective (sixFourExternalPoint H) := by
  intro i j hij
  apply (sixFourDegreeThreeEquiv H).injective
  apply Subtype.ext
  exact hij

/-- Each external point carries exactly three of the six base supports. -/
theorem sixFourExternalPoint_basesThrough_card
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (i : Fin 2) :
    (sixFourBasesThrough B (sixFourExternalPoint H i)).card = 3 := by
  rw [sixFourBasesThrough_card, sixFourExternalPoint_degree_eq_three]

/-- A numbered copy of the three base indices through an external point. -/
noncomputable def sixFourExternalBasesEquiv
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (i : Fin 2) :
    Fin 3 ≃ ↥(sixFourBasesThrough B (sixFourExternalPoint H i)) := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  simpa only [Fintype.card_coe] using sixFourExternalPoint_basesThrough_card H i

/-- The actual base index in a numbered external fibre. -/
noncomputable def sixFourExternalBase
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (i : Fin 2) (r : Fin 3) : Fin 6 :=
  (sixFourExternalBasesEquiv H i r).1

/-- Each numbered external base contains the corresponding external point. -/
theorem sixFourExternalPoint_mem_externalBase
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (i : Fin 2) (r : Fin 3) :
    sixFourExternalPoint H i ∈ B (sixFourExternalBase H i r) :=
  mem_sixFourBasesThrough.mp (sixFourExternalBasesEquiv H i r).2

/-- The numbered bases in one external fibre are distinct. -/
theorem sixFourExternalBase_injective
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (i : Fin 2) :
    Function.Injective (sixFourExternalBase H i) := by
  intro r s hrs
  apply (sixFourExternalBasesEquiv H i).injective
  apply Subtype.ext
  exact hrs

/-- Two distinct bases have at most one common selected point.  This is the
pointwise form of the saturated pair-intersection theorem used below to make
crossing points unique. -/
theorem sixFour_common_point_eq
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    {i j : Fin 6} (hij : i ≠ j) {x y : Point}
    (hxi : x ∈ B i) (hxj : x ∈ B j)
    (hyi : y ∈ B i) (hyj : y ∈ B j) : x = y := by
  have hinter : (B i ∩ B j).card = 1 := sixFour_pair_inter_eq_one H i j hij
  by_contra hxy
  have hsub : ({x, y} : Finset Point) ⊆ B i ∩ B j := by
    intro z hz
    have hcases : z = x ∨ z = y := by simpa using hz
    rcases hcases with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxi, hxj⟩
    · exact Finset.mem_inter.mpr ⟨hyi, hyj⟩
  have hcard := Finset.card_le_card hsub
  have hpair : ({x, y} : Finset Point).card = 2 := by simp [hxy]
  rw [hpair, hinter] at hcard
  omega

/-- Every two distinct bases have a selected common point. -/
theorem sixFour_pair_inter_nonempty
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    {i j : Fin 6} (hij : i ≠ j) :
    ∃ x : Point, x ∈ B i ∧ x ∈ B j := by
  have hcard : (B i ∩ B j).card = 1 := sixFour_pair_inter_eq_one H i j hij
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
  exact ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩

/-- A fixed finite representative of the unique common point of two distinct
bases. -/
noncomputable def sixFourPairIntersectionPoint
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (i j : Fin 6) (hij : i ≠ j) : Point :=
  Classical.choose (sixFour_pair_inter_nonempty H hij)

theorem sixFourPairIntersectionPoint_mem_left
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (i j : Fin 6) (hij : i ≠ j) :
    sixFourPairIntersectionPoint H i j hij ∈ B i :=
  (Classical.choose_spec (sixFour_pair_inter_nonempty H hij)).1

theorem sixFourPairIntersectionPoint_mem_right
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (i j : Fin 6) (hij : i ≠ j) :
    sixFourPairIntersectionPoint H i j hij ∈ B j :=
  (Classical.choose_spec (sixFour_pair_inter_nonempty H hij)).2

/-- Any common point of a distinct pair of bases is its chosen intersection
representative. -/
theorem sixFourPairIntersectionPoint_eq_of_mem
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    {i j : Fin 6} (hij : i ≠ j) {x : Point}
    (hxi : x ∈ B i) (hxj : x ∈ B j) :
    x = sixFourPairIntersectionPoint H i j hij := by
  apply sixFour_common_point_eq H hij hxi hxj
  · exact sixFourPairIntersectionPoint_mem_left H i j hij
  · exact sixFourPairIntersectionPoint_mem_right H i j hij

/-- Saturation excludes a point carried by exactly one base. -/
theorem sixFour_degree_ne_one
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (x : Point) :
    sixFourDegree B x ≠ 1 := by
  rcases sixFour_degree_eq_two_or_three H x with hx | hx <;> omega

/-- A four-point base has a fourth point away from any three distinct listed
members. -/
theorem sixFour_exists_fourth_point
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (i : Fin 6)
    {x y z : Point} (hxi : x ∈ B i) (hyi : y ∈ B i) (hzi : z ∈ B i)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : Point, c ∈ B i ∧ c ≠ x ∧ c ≠ y ∧ c ≠ z := by
  by_contra hnone
  push_neg at hnone
  have hsub : B i ⊆ ({x, y, z} : Finset Point) := by
    intro c hc
    by_cases hcx : c = x
    · simpa [hcx]
    by_cases hcy : c = y
    · simpa [hcy]
    have hcz : c = z := hnone c hc hcx hcy
    simpa [hcz]
  have hle := Finset.card_le_card hsub
  have htriple : ({x, y, z} : Finset Point).card = 3 := by
    simp [hxy, hxz, hyz]
  rw [H.base_card i, htriple] at hle
  omega

/-- If a selected point belongs to one specified base and to no other one,
its six-four degree is one. -/
theorem sixFour_degree_eq_one_of_unique_base
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} {x : Point} {i : Fin 6}
    (hxi : x ∈ B i) (hunique : ∀ j : Fin 6, x ∈ B j -> j = i) :
    sixFourDegree B x = 1 := by
  change ((Finset.univ : Finset (Fin 6)).filter fun j => x ∈ B j).card = 1
  have hfilter : (Finset.univ : Finset (Fin 6)).filter (fun j => x ∈ B j) =
      ({i} : Finset (Fin 6)) := by
    ext j
    constructor
    · intro hj
      have hxj := Finset.mem_filter.mp hj
      have hji := hunique j hxj.2
      simpa [hji]
    · intro hj
      have hji : j = i := by simpa using hj
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩
  rw [hfilter]
  simp

/-- Every selected point has a second base through it.  This packages the
``no degree-one point'' consequence in the form needed by the grid argument. -/
theorem sixFour_exists_other_base
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    {x : Point} {i : Fin 6} (hxi : x ∈ B i) :
    ∃ j : Fin 6, j ≠ i ∧ x ∈ B j := by
  by_contra hnone
  have hunique : ∀ j : Fin 6, x ∈ B j → j = i := by
    intro j hxj
    by_contra hji
    exact hnone ⟨j, hji, hxj⟩
  exact (sixFour_degree_ne_one H x)
    (sixFour_degree_eq_one_of_unique_base hxi hunique)

/-- The three bases through either degree-three point are disjoint from the
three bases through the other one.  Were a base common to both fibres, its two
remaining points would both need the unique sixth base, contradicting the
one-point intersection of that pair of bases. -/
theorem sixFourExternalBases_disjoint
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    Disjoint (sixFourBasesThrough B (sixFourExternalPoint H 0))
      (sixFourBasesThrough B (sixFourExternalPoint H 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro i hi0 hi1
  have he0i : sixFourExternalPoint H 0 ∈ B i := mem_sixFourBasesThrough.mp hi0
  have he1i : sixFourExternalPoint H 1 ∈ B i := mem_sixFourBasesThrough.mp hi1
  have hext_ne : sixFourExternalPoint H 0 ≠ sixFourExternalPoint H 1 := by
    intro heq
    have h01 : (0 : Fin 2) = 1 := sixFourExternalPoint_injective H heq
    norm_num at h01
  let A := sixFourBasesThrough B (sixFourExternalPoint H 0)
  let C := sixFourBasesThrough B (sixFourExternalPoint H 1)
  have hAc : A ∩ C = ({i} : Finset (Fin 6)) := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · intro hk
      have hk0 : sixFourExternalPoint H 0 ∈ B k :=
        mem_sixFourBasesThrough.mp hk.1
      have hk1 : sixFourExternalPoint H 1 ∈ B k :=
        mem_sixFourBasesThrough.mp hk.2
      by_cases hki : k = i
      · simpa [hki]
      · have heq : sixFourExternalPoint H 0 = sixFourExternalPoint H 1 :=
          sixFour_common_point_eq H hki hk0 he0i hk1 he1i
        exact False.elim (hext_ne heq)
    · intro hk
      subst k
      exact ⟨hi0, hi1⟩
  have hAcard : A.card = 3 := by
    simpa [A] using sixFourExternalPoint_basesThrough_card H 0
  have hCcard : C.card = 3 := by
    simpa [C] using sixFourExternalPoint_basesThrough_card H 1
  have hUcard : (A ∪ C).card = 5 := by
    have hcard := Finset.card_union_add_card_inter A C
    rw [hAcard, hCcard, hAc] at hcard
    norm_num at hcard ⊢
    omega
  have hcompcard : ((Finset.univ : Finset (Fin 6)) \ (A ∪ C)).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hUcard]
    norm_num
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcompcard
  have hz_exists : ∃ z : Point, z ∈ B i ∧ z ≠ sixFourExternalPoint H 0 ∧
      z ≠ sixFourExternalPoint H 1 := by
    by_contra hnone
    have hsub : B i ⊆ ({sixFourExternalPoint H 0,
        sixFourExternalPoint H 1} : Finset Point) := by
      intro z hz
      by_cases hz0 : z = sixFourExternalPoint H 0
      · simpa [hz0]
      by_cases hz1 : z = sixFourExternalPoint H 1
      · simpa [hz1]
      exact False.elim (hnone ⟨z, hz, hz0, hz1⟩)
    have hle := Finset.card_le_card hsub
    have hpair : ({sixFourExternalPoint H 0,
        sixFourExternalPoint H 1} : Finset Point).card = 2 := by
      simp [hext_ne]
    rw [H.base_card i, hpair] at hle
    omega
  obtain ⟨z, hzi, hz0, hz1⟩ := hz_exists
  obtain ⟨c, hci, hc0, hc1, hcz⟩ := sixFour_exists_fourth_point H i
    he0i he1i hzi hext_ne (Ne.symm hz0) (Ne.symm hz1)
  obtain ⟨j, hji, hzj⟩ := sixFour_exists_other_base H hzi
  obtain ⟨k, hki, hck⟩ := sixFour_exists_other_base H hci
  have hjA : j ∉ A := by
    intro hj
    have hj0 : sixFourExternalPoint H 0 ∈ B j := mem_sixFourBasesThrough.mp hj
    have hz_eq : z = sixFourExternalPoint H 0 :=
      sixFour_common_point_eq H hji hzj hzi hj0 he0i
    exact hz0 hz_eq
  have hjC : j ∉ C := by
    intro hj
    have hj1 : sixFourExternalPoint H 1 ∈ B j := mem_sixFourBasesThrough.mp hj
    have hz_eq : z = sixFourExternalPoint H 1 :=
      sixFour_common_point_eq H hji hzj hzi hj1 he1i
    exact hz1 hz_eq
  have hkA : k ∉ A := by
    intro hk
    have hk0 : sixFourExternalPoint H 0 ∈ B k := mem_sixFourBasesThrough.mp hk
    have hc_eq : c = sixFourExternalPoint H 0 :=
      sixFour_common_point_eq H hki hck hci hk0 he0i
    exact hc0 hc_eq
  have hkC : k ∉ C := by
    intro hk
    have hk1 : sixFourExternalPoint H 1 ∈ B k := mem_sixFourBasesThrough.mp hk
    have hc_eq : c = sixFourExternalPoint H 1 :=
      sixFour_common_point_eq H hki hck hci hk1 he1i
    exact hc1 hc_eq
  have hjq : j = q := by
    have hjcomp : j ∈ (Finset.univ : Finset (Fin 6)) \ (A ∪ C) := by
      simp [hjA, hjC]
    simpa [hq] using hjcomp
  have hkq : k = q := by
    have hkcomp : k ∈ (Finset.univ : Finset (Fin 6)) \ (A ∪ C) := by
      simp [hkA, hkC]
    simpa [hq] using hkcomp
  have hjk : j = k := hjq.trans hkq.symm
  have hzk : z ∈ B k := by simpa [← hjk] using hzj
  have hzc : z = c := sixFour_common_point_eq H hki hzk hzi hck hci
  exact hcz hzc.symm

/-- A row base and a column base are different, because the two external
fibres are disjoint. -/
theorem sixFourExternalBase_zero_ne_one
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (r s : Fin 3) :
    sixFourExternalBase H 0 r ≠ sixFourExternalBase H 1 s := by
  intro hrs
  have hdis := Finset.disjoint_left.mp (sixFourExternalBases_disjoint H)
  apply hdis
  · exact mem_sixFourBasesThrough.mpr
      (sixFourExternalPoint_mem_externalBase H 0 r)
  · simpa [hrs] using (mem_sixFourBasesThrough.mpr
      (sixFourExternalPoint_mem_externalBase H 1 s))

/-- The canonical selected point at the crossing of a numbered row and
numbered column. -/
noncomputable def sixFourGridPoint
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (r s : Fin 3) : Point :=
  sixFourPairIntersectionPoint H (sixFourExternalBase H 0 r)
    (sixFourExternalBase H 1 s) (sixFourExternalBase_zero_ne_one H r s)

theorem sixFourGridPoint_mem_row
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (r s : Fin 3) :
    sixFourGridPoint H r s ∈ B (sixFourExternalBase H 0 r) := by
  simpa [sixFourGridPoint] using sixFourPairIntersectionPoint_mem_left H
    (sixFourExternalBase H 0 r) (sixFourExternalBase H 1 s)
      (sixFourExternalBase_zero_ne_one H r s)

theorem sixFourGridPoint_mem_column
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (r s : Fin 3) :
    sixFourGridPoint H r s ∈ B (sixFourExternalBase H 1 s) := by
  simpa [sixFourGridPoint] using sixFourPairIntersectionPoint_mem_right H
    (sixFourExternalBase H 0 r) (sixFourExternalBase H 1 s)
      (sixFourExternalBase_zero_ne_one H r s)

/-- The two degree-three points are precisely the extracted external pair. -/
theorem sixFour_degree_eq_three_iff_external
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (x : Point) :
    sixFourDegree B x = 3 ↔ ∃ i : Fin 2, sixFourExternalPoint H i = x := by
  constructor
  · intro hx
    have hxmem : x ∈ sixFourDegreeThree B :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    obtain ⟨i, hi⟩ := (sixFourDegreeThreeEquiv H).surjective ⟨x, hxmem⟩
    refine ⟨i, ?_⟩
    simpa [sixFourExternalPoint] using congrArg Subtype.val hi
  · rintro ⟨i, rfl⟩
    exact sixFourExternalPoint_degree_eq_three H i

private theorem sixFourExternalPoint_zero_not_mem_column
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (s : Fin 3) :
    sixFourExternalPoint H 0 ∉ B (sixFourExternalBase H 1 s) := by
  intro hmem
  have hdis := Finset.disjoint_left.mp (sixFourExternalBases_disjoint H)
  exact hdis
    (mem_sixFourBasesThrough.mpr hmem)
    (mem_sixFourBasesThrough.mpr (sixFourExternalPoint_mem_externalBase H 1 s))

private theorem sixFourExternalPoint_one_not_mem_row
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (r : Fin 3) :
    sixFourExternalPoint H 1 ∉ B (sixFourExternalBase H 0 r) := by
  intro hmem
  have hdis := Finset.disjoint_left.mp (sixFourExternalBases_disjoint H)
  exact hdis
    (mem_sixFourBasesThrough.mpr (sixFourExternalPoint_mem_externalBase H 0 r))
    (mem_sixFourBasesThrough.mpr hmem)

/-- Every row-column crossing is one of the nine degree-two points. -/
theorem sixFourGridPoint_degree_eq_two
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B)
    (r s : Fin 3) : sixFourDegree B (sixFourGridPoint H r s) = 2 := by
  rcases sixFour_degree_eq_two_or_three H (sixFourGridPoint H r s) with htwo | hthree
  · exact htwo
  · obtain ⟨i, hi⟩ := (sixFour_degree_eq_three_iff_external H _).mp hthree
    fin_cases i
    · have hmem := sixFourGridPoint_mem_column H r s
      rw [← hi] at hmem
      exact False.elim (sixFourExternalPoint_zero_not_mem_column H s hmem)
    · have hmem := sixFourGridPoint_mem_row H r s
      rw [← hi] at hmem
      exact False.elim (sixFourExternalPoint_one_not_mem_row H r hmem)

/-- The nine row-column crossings have distinct ordered row/column labels. -/
theorem sixFourGridPoint_injective
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    Function.Injective (fun rs : Fin 3 × Fin 3 => sixFourGridPoint H rs.1 rs.2) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ heq
  have heq' : sixFourGridPoint H r s = sixFourGridPoint H r' s' := by
    simpa using heq
  have hrow : r = r' := by
    by_contra hrr
    have hbase : sixFourExternalBase H 0 r ≠ sixFourExternalBase H 0 r' := by
      intro hbase
      exact hrr (sixFourExternalBase_injective H 0 hbase)
    have hmemr := sixFourGridPoint_mem_row H r s
    have hmemr' := sixFourGridPoint_mem_row H r' s'
    rw [heq'] at hmemr
    have hx : sixFourGridPoint H r' s' = sixFourExternalPoint H 0 :=
      sixFour_common_point_eq H hbase hmemr hmemr'
        (sixFourExternalPoint_mem_externalBase H 0 r)
        (sixFourExternalPoint_mem_externalBase H 0 r')
    have hcol := sixFourGridPoint_mem_column H r' s'
    rw [hx] at hcol
    exact sixFourExternalPoint_zero_not_mem_column H s' hcol
  have hcolumn : s = s' := by
    by_contra hss
    have hbase : sixFourExternalBase H 1 s ≠ sixFourExternalBase H 1 s' := by
      intro hbase
      exact hss (sixFourExternalBase_injective H 1 hbase)
    have hmems := sixFourGridPoint_mem_column H r s
    have hmems' := sixFourGridPoint_mem_column H r' s'
    rw [heq'] at hmems
    have hx : sixFourGridPoint H r' s' = sixFourExternalPoint H 1 :=
      sixFour_common_point_eq H hbase hmems hmems'
        (sixFourExternalPoint_mem_externalBase H 1 s)
        (sixFourExternalPoint_mem_externalBase H 1 s')
    have hrowmem := sixFourGridPoint_mem_row H r' s'
    rw [hx] at hrowmem
    exact sixFourExternalPoint_one_not_mem_row H r' hrowmem
  exact Prod.ext hrow hcolumn

/-- The canonical nine-point grid as a finite image. -/
noncomputable def sixFourGridImage
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) : Finset Point :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image
    (fun rs => sixFourGridPoint H rs.1 rs.2)

theorem sixFourGridImage_eq_degreeTwo
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    sixFourGridImage H = sixFourDegreeTwo B := by
  have hsubset : sixFourGridImage H ⊆ sixFourDegreeTwo B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨rs, _hrs, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      sixFourGridPoint_degree_eq_two H rs.1 rs.2⟩
  have hcard : (sixFourDegreeTwo B).card ≤ (sixFourGridImage H).card := by
    rw [sixFourGridImage, Finset.card_image_of_injective _
      (sixFourGridPoint_injective H), Finset.card_univ]
    have hdegreeTwo := (sixFour_degree_profile H).2.1
    norm_num at hdegreeTwo ⊢
    omega
  exact Finset.eq_of_subset_of_card_le hsubset hcard

/-- The lossless finite data immediately available before proving the two
three-base fibres disjoint and relabelling them as rows and columns. -/
structure SixFourExternalEntrance
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (B : Fin 6 -> Finset Point) : Type u where
  external : Fin 2 -> Point
  external_injective : Function.Injective external
  external_degree : ∀ i, sixFourDegree B (external i) = 3
  external_fibre_card : ∀ i, (sixFourBasesThrough B (external i)).card = 3
  pair_inter_one : ∀ i j, i ≠ j -> (B i ∩ B j).card = 1
  degree_two_or_three : ∀ x, sixFourDegree B x = 2 ∨ sixFourDegree B x = 3

/-- Construct the external-point entrance from the saturated moment wall. -/
noncomputable def sixFourExternalEntrance_of_saturated
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    SixFourExternalEntrance B where
  external := sixFourExternalPoint H
  external_injective := sixFourExternalPoint_injective H
  external_degree := sixFourExternalPoint_degree_eq_three H
  external_fibre_card := sixFourExternalPoint_basesThrough_card H
  pair_inter_one := sixFour_pair_inter_eq_one H
  degree_two_or_three := (sixFour_degree_profile H).2.2

end Erdos506.Finite
