import Erdos506.Finite.UngarSixAllowableSequence
import Erdos506.V3.Construction
import Erdos506.Incidence.SixConicActiveSignatureGeometry

/-!
# The sharp parallel-chord case for six points on a circle

The rotating-line argument for a six-point circle has a very small finite
core.  A fixed direction gives a matching of the six labels: two chords of a
circle with the same direction cannot share an endpoint, since otherwise
three distinct points of the circle would be collinear.  Hence a direction
has at most three chords.  The counting lemma in
`Finite.UngarSixAllowableSequence` then shows that the only possible failure
of the six-direction bound is five perfect matchings.

This file records the matching half independently of a choice of circle
coordinates.  The remaining geometric sharp case is therefore exactly the
claim that five parallel-chord perfect matchings on one proper circle cannot
account for all fifteen chords with only five directions.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

/-- A pairwise-disjoint family of two-subsets of six labels has at most
three members.  This is the finite matching bound used for one parallel
class of chords. -/
theorem card_le_three_of_pairwiseDisjoint_kSubsetTwo_finSix
    (C : Finset (KSubset (Fin 6) 2))
    (hdisjoint : (C : Set (KSubset (Fin 6) 2)).PairwiseDisjoint
      (fun A => A.1)) :
    C.card ≤ 3 := by
  have hsubset : C.biUnion (fun A => A.1) ⊆ (Finset.univ : Finset (Fin 6)) :=
    fun _ _ => Finset.mem_univ _
  have hcardUnion : (C.biUnion fun A => A.1).card =
      ∑ A ∈ C, A.1.card := Finset.card_biUnion hdisjoint
  have hcardTwo : ∑ A ∈ C, A.1.card = C.card * 2 := by
    calc
      ∑ A ∈ C, A.1.card = ∑ _A ∈ C, 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact A.2
      _ = C.card * 2 := by simp [Nat.mul_comm]
  have hbound : C.card * 2 ≤ 6 := by
    calc
      C.card * 2 = (C.biUnion fun A => A.1).card := by
        rw [hcardUnion, hcardTwo]
      _ ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_le_card hsubset
      _ = 6 := by simp
  omega

/-- The exact finite interface produced by the circle geometry: a direction
class is a matching of the six labelled circle points.  Once this is proved
for each direction, the preceding lemma supplies the required cap three. -/
def DirectionClassIsMatching
    (cfg : Configuration (Fin 6)) (D : Submodule ℝ Point2) : Prop :=
  ((directionPairClass cfg D : Finset (KSubset (Fin 6) 2)) :
    Set (KSubset (Fin 6) 2)).PairwiseDisjoint (fun A => A.1)

/-- Two equal-direction chords through one selected point of a proper
circle are the same chord.  The proof uses only the line--circle fact that
three distinct points of a proper circle are not collinear. -/
private theorem kSubsetTwo_eq_of_common_mem_of_same_direction_on_circle
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (hc : ∀ i, cfg i ∈ (c.1 : Set Point2))
    {A B : KSubset (Fin 6) 2}
    (hdir : directionOfPair cfg A = directionOfPair cfg B)
    {x : Fin 6} (hxA : x ∈ A.1) (hxB : x ∈ B.1) :
    A = B := by
  classical
  have hAerase : (A.1.erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxA, A.2]
  have hBerase : (B.1.erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hxB, B.2]
  obtain ⟨y, hAother⟩ := Finset.card_eq_one.mp hAerase
  obtain ⟨z, hBother⟩ := Finset.card_eq_one.mp hBerase
  have hxy : x ≠ y := by
    intro hxy
    subst y
    have : x ∈ A.1.erase x := by simpa [hAother]
    exact (Finset.mem_erase.mp this).1 rfl
  have hxz : x ≠ z := by
    intro hxz
    subst z
    have : x ∈ B.1.erase x := by simpa [hBother]
    exact (Finset.mem_erase.mp this).1 rfl
  have hAeq : A.1 = {x, y} := by
    calc
      A.1 = insert x (A.1.erase x) := (Finset.insert_erase hxA).symm
      _ = {x, y} := by rw [hAother]
  have hBeq : B.1 = {x, z} := by
    calc
      B.1 = insert x (B.1.erase x) := (Finset.insert_erase hxB).symm
      _ = {x, z} := by rw [hBother]
  have hAsub : A = ⟨{x, y}, by simp [hxy]⟩ := Subtype.ext hAeq
  have hBsub : B = ⟨{x, z}, by simp [hxz]⟩ := Subtype.ext hBeq
  by_cases hyz : y = z
  · apply Subtype.ext
    rw [hAeq, hBeq, hyz]
  · have hdir' :
        directionOfPoints (cfg x) (cfg y) =
          directionOfPoints (cfg x) (cfg z) := by
      rw [hAsub, hBsub] at hdir
      simpa only [directionOfPair_eq_directionOfPoints cfg hxy,
        directionOfPair_eq_directionOfPoints cfg hxz] using hdir
    have hcol : Collinear ℝ ({cfg x, cfg y, cfg z} : Set Point2) :=
      collinear_of_directionOfPoints_eq hdir'
    exact False.elim ((Erdos506.V3.not_collinear_three_distinct_on_sphere
      (hc x) (hc y) (hc z)
      (cfg.injective.ne hxy) (cfg.injective.ne hxz)
      (cfg.injective.ne hyz)) hcol)

/-- Every parallel class of chords among six distinct selected points on a
proper circle is a matching. -/
theorem directionClassIsMatching_of_all_mem_properCircle
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (hc : ∀ i, cfg i ∈ (c.1 : Set Point2)) (D : Submodule ℝ Point2) :
    DirectionClassIsMatching cfg D := by
  classical
  intro A hA B hB hAB
  apply Finset.disjoint_left.2
  intro x hxA hxB
  apply hAB
  apply kSubsetTwo_eq_of_common_mem_of_same_direction_on_circle cfg c hc
    ((Finset.mem_filter.mp hA).2.trans (Finset.mem_filter.mp hB).2.symm) (by
      exact hxA) (by exact hxB)

/-- A six-point circle trace contains every label of a `Fin 6`
configuration, so its equal-direction pair classes have cardinality at most
three.  This is the geometric cap required by the sharp counting reduction. -/
theorem directionPairClass_card_le_three_of_circleTrace_card_six
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (htrace : (circleTrace cfg c).card = 6) (D : Submodule ℝ Point2) :
    (directionPairClass cfg D).card ≤ 3 := by
  classical
  have hfull : circleTrace cfg c = (Finset.univ : Finset (Fin 6)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [htrace]
  apply card_le_three_of_pairwiseDisjoint_kSubsetTwo_finSix
    (directionPairClass cfg D)
  apply directionClassIsMatching_of_all_mem_properCircle cfg c
  intro i
  exact mem_circleTrace.mp (by simpa [hfull])

/-- The combinatorial conclusion of the parallel-chord matching interface. -/
theorem directionPairClass_card_le_three_of_isMatching
    (cfg : Configuration (Fin 6)) (D : Submodule ℝ Point2)
    (hmatching : DirectionClassIsMatching cfg D) :
    (directionPairClass cfg D).card ≤ 3 := by
  exact card_le_three_of_pairwiseDisjoint_kSubsetTwo_finSix
    (directionPairClass cfg D) hmatching

/-- Equality in the matching cap is literally a perfect matching: its three
chords cover all six labels.  This is the exact finite form of the residual
sharp case that the circle-reflection argument has to rule out. -/
theorem directionPairClass_biUnion_eq_univ_of_isMatching_of_card_three
    (cfg : Configuration (Fin 6)) (D : Submodule ℝ Point2)
    (hmatching : DirectionClassIsMatching cfg D)
    (hcard : (directionPairClass cfg D).card = 3) :
    (directionPairClass cfg D).biUnion (fun A => A.1) =
      (Finset.univ : Finset (Fin 6)) := by
  classical
  let C := directionPairClass cfg D
  have hsum : ∑ A ∈ C, A.1.card = 6 := by
    calc
      ∑ A ∈ C, A.1.card = ∑ _A ∈ C, 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact A.2
      _ = C.card * 2 := by simp [Nat.mul_comm]
      _ = 6 := by rw [hcard]
  have hunion : (C.biUnion fun A => A.1).card = 6 := by
    rw [Finset.card_biUnion hmatching, hsum]
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [C, hunion]

/-! ## The projective form of a parallel class -/

/-- A chord contains its own point at infinity.  This is the elementary
coordinate bridge which turns equality of affine directions into the common
centre required by the six-conic involution classifier. -/
private theorem pointAtInfinity_orthogonal_projectiveLine
    {p q : Point2} (hpq : p ≠ q) :
    Projectivization.orthogonal
      (pointAtInfinity (q - p) (sub_ne_zero.mpr hpq.symm))
      (projectiveLine p q hpq) := by
  change directionLift (q - p) ⬝ᵥ lineCovector p q = 0
  simp only [directionLift, lineCovector_eq_vec, dotProduct,
    Fin.sum_univ_three, PiLp.sub_apply]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> ring

/-- Equal one-dimensional affine directions have the same projective point
at infinity.  The unit supplied by equality of singleton spans is exactly
the projective rescaling. -/
private theorem pointAtInfinity_eq_of_directionOfPoints_eq
    {p q r s : Point2} (hpq : p ≠ q) (hrs : r ≠ s)
    (hdir : directionOfPoints p q = directionOfPoints r s) :
    pointAtInfinity (q - p) (sub_ne_zero.mpr hpq.symm) =
      pointAtInfinity (s - r) (sub_ne_zero.mpr hrs.symm) := by
  have hqp0 : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hsr0 : s - r ≠ 0 := sub_ne_zero.mpr hrs.symm
  unfold directionOfPoints at hdir
  rw [Submodule.span_singleton_eq_span_singleton] at hdir
  obtain ⟨u, hu⟩ := hdir
  have hu' : (u : ℝ) • (q - p) = s - r := by
    simpa only [Units.smul_def] using hu
  have huinv : ((u⁻¹ : ℝˣ) : ℝ) • (s - r) = q - p := by
    rw [← hu']
    simp [smul_smul]
  apply (Projectivization.mk_eq_mk_iff' ℝ
    (directionLift (q - p)) (directionLift (s - r))
    (directionLift_ne_zero hqp0) (directionLift_ne_zero hsr0)).2
  refine ⟨u⁻¹, ?_⟩
  ext i
  fin_cases i
  · simpa [directionLift, Pi.smul_apply, PiLp.smul_apply] using
      congrArg (fun w : Point2 => w 0) huinv
  · simpa [directionLift, Pi.smul_apply, PiLp.smul_apply] using
      congrArg (fun w : Point2 => w 1) huinv
  · simp [directionLift, Pi.smul_apply]

/-- The value-level family of pairs in one direction class.  The classifier
works with finite sets rather than the `KSubset` wrapper used by the
allowable-sequence count. -/
noncomputable def directionPairMatching
    (cfg : Configuration (Fin 6)) (D : Submodule ℝ Point2) :
    Finset (Finset (Fin 6)) :=
  (directionPairClass cfg D).image Subtype.val

/-- Equality in the matching cap gives a genuine perfect matching on the
circle trace, in the exact representation consumed by the conic classifier. -/
theorem directionPairMatching_isPerfectMatchingOn_of_card_three
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (htrace : (circleTrace cfg c).card = 6) (D : Submodule ℝ Point2)
    (hcard : (directionPairClass cfg D).card = 3) :
    SixConicPerfectMatchingOn (circleTrace cfg c)
      (directionPairMatching cfg D) := by
  classical
  have hfull : circleTrace cfg c = (Finset.univ : Finset (Fin 6)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [htrace]
  have hdisjoint := directionClassIsMatching_of_all_mem_properCircle
    cfg c (by
      intro i
      exact mem_circleTrace.mp (by simpa [hfull])) D
  have hcover := directionPairClass_biUnion_eq_univ_of_isMatching_of_card_three
    cfg D hdisjoint hcard
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨A.2, by simpa [hfull]⟩
  · intro p hp q hq hpq
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hq
    apply hdisjoint hA hB
    intro hAB
    apply hpq
    exact congrArg Subtype.val hAB
  · calc
      (directionPairMatching cfg D).biUnion id =
          (directionPairClass cfg D).biUnion (fun A => A.1) := by
        simp [directionPairMatching, Finset.image_biUnion]
      _ = Finset.univ := hcover
      _ = circleTrace cfg c := hfull.symm

/-- The equality case for one parallel class is one of the four dihedral
matchings of the marked circle.  Its common projective centre is simply the
point at infinity of any one of its chords. -/
theorem directionPairMatching_dihedral_of_card_three
    (cfg : Configuration (Fin 6)) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (htrace : (circleTrace cfg gamma.1).card = 6) (D : Submodule ℝ Point2)
    (hcard : (directionPairClass cfg D).card = 3) :
    ∃ code : SixCycleInvolutionCode,
      directionPairMatching cfg D = relabelSixCycleMatching
        (fun i => (sixConicCyclicLabel cfg gamma htrace i).1) code := by
  classical
  have hnonempty : (directionPairClass cfg D).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have : (directionPairClass cfg D).card = 0 := by simp [hempty]
    omega
  obtain ⟨A, hA⟩ := hnonempty
  obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp A.2
  have hAi : A = ⟨{i, j}, by simp [hij]⟩ := Subtype.ext hAeq
  have hdirA : directionOfPoints (cfg i) (cfg j) = D := by
    rw [← directionOfPair_eq_directionOfPoints cfg hij, ← hAi]
    exact (Finset.mem_filter.mp hA).2
  let v : Point2 := cfg j - cfg i
  have hv : v ≠ 0 := by
    exact sub_ne_zero.mpr (cfg.injective.ne hij.symm)
  let O : RealProjectivePlane := pointAtInfinity v hv
  have hnondegenerate : properCirclePencilDeterminant gamma.1 O.rep ≠ 0 := by
    exact properCirclePencilDeterminant_pointAtInfinity_ne_zero gamma.1 v hv
  apply sixConic_commonCenterPerfectMatching_dihedral cfg gamma htrace
    (directionPairMatching cfg D)
    (directionPairMatching_isPerfectMatchingOn_of_card_three
      cfg gamma.1 htrace D hcard)
    O hnondegenerate
  intro a b hab hpair
  obtain ⟨B, hB, hBval⟩ := Finset.mem_image.mp hpair
  have habVal : a.1 ≠ b.1 := Subtype.val_injective.ne hab
  have hBpair : B = ⟨{a.1, b.1}, by simp [habVal]⟩ := Subtype.ext hBval
  have hdirB : directionOfPoints (cfg a.1) (cfg b.1) = D := by
    rw [← directionOfPair_eq_directionOfPoints cfg habVal, ← hBpair]
    exact (Finset.mem_filter.mp hB).2
  have hOeq : O = pointAtInfinity (cfg b.1 - cfg a.1)
      (sub_ne_zero.mpr (cfg.injective.ne habVal).symm) := by
    dsimp [O, v]
    apply pointAtInfinity_eq_of_directionOfPoints_eq
    · exact cfg.injective.ne hij
    · exact cfg.injective.ne habVal
    · exact hdirA.trans hdirB.symm
  rw [hOeq]
  exact pointAtInfinity_orthogonal_projectiveLine (cfg.injective.ne habVal)

/-- The four dihedral matchings leave no room for five distinct perfect
parallel classes.  Together with the fifteen-pair count this closes the
sharp case on a determined six-point circle. -/
theorem six_le_card_determinedDirections_of_determinedCircleTrace_card_six
    (cfg : Configuration (Fin 6)) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (htrace : (circleTrace cfg gamma.1).card = 6) :
    6 ≤ (determinedDirections cfg).card := by
  classical
  by_contra hgoal
  have hcapacity : ∀ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 3 := by
    intro D hD
    exact directionPairClass_card_le_three_of_circleTrace_card_six
      cfg gamma.1 htrace D
  have hnotSmall : ¬ ∃ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 2 := by
    intro hsmall
    exact hgoal
      (six_le_card_determinedDirections_of_pair_class_cap_three
        cfg hcapacity hsmall)
  have hthree : ∀ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card = 3 := by
    intro D hD
    have hcap := hcapacity D hD
    apply Nat.le_antisymm hcap
    by_contra hlt
    have hsmall : (directionPairClass cfg D).card ≤ 2 := by omega
    exact hnotSmall ⟨D, hD, hsmall⟩
  let code : {D : Submodule ℝ Point2 // D ∈ determinedDirections cfg} →
      SixCycleInvolutionCode := fun D =>
    (directionPairMatching_dihedral_of_card_three cfg gamma htrace D.1
      (hthree D.1 D.2)).choose
  have hcode : ∀ D : {D : Submodule ℝ Point2 // D ∈ determinedDirections cfg},
      directionPairMatching cfg D.1 = relabelSixCycleMatching
        (fun i => (sixConicCyclicLabel cfg gamma htrace i).1) (code D) := by
    intro D
    exact (directionPairMatching_dihedral_of_card_three cfg gamma htrace D.1
      (hthree D.1 D.2)).choose_spec
  have hcode_injective : Function.Injective code := by
    intro D E hDE
    have hmatching : directionPairMatching cfg D.1 =
        directionPairMatching cfg E.1 := by
      calc
        directionPairMatching cfg D.1 = relabelSixCycleMatching
            (fun i => (sixConicCyclicLabel cfg gamma htrace i).1) (code D) :=
          hcode D
        _ = relabelSixCycleMatching
            (fun i => (sixConicCyclicLabel cfg gamma htrace i).1) (code E) := by
          rw [hDE]
        _ = directionPairMatching cfg E.1 := (hcode E).symm
    have hDnonempty : (directionPairClass cfg D.1).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      have : (directionPairClass cfg D.1).card = 0 := by simp [hempty]
      have hDthree := hthree D.1 D.2
      omega
    obtain ⟨A, hA⟩ := hDnonempty
    have hAval : A.1 ∈ directionPairMatching cfg E.1 := by
      rw [← hmatching]
      exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
    obtain ⟨B, hB, hBA⟩ := Finset.mem_image.mp hAval
    have hBA' : B = A := Subtype.ext hBA
    apply Subtype.ext
    calc
      D.1 = directionOfPair cfg A := (Finset.mem_filter.mp hA).2.symm
      _ = directionOfPair cfg B := by rw [hBA']
      _ = E.1 := (Finset.mem_filter.mp hB).2
  have hdirCard : (determinedDirections cfg).card ≤ 4 := by
    have hsubtypeCard : Fintype.card
        {D : Submodule ℝ Point2 // D ∈ determinedDirections cfg} ≤
        Fintype.card SixCycleInvolutionCode :=
      Fintype.card_le_of_injective code hcode_injective
    simpa using hsubtypeCard
  have hcount := card_kSubset_two_le_direction_capacity_mul cfg 3 hcapacity
  have hchoose : Nat.choose 6 2 = 15 := by decide
  have hpairs : Fintype.card (KSubset (Fin 6) 2) = 15 := by
    rw [card_kSubset]
    simpa using hchoose
  omega

/-- A proper circle carrying all six labels is automatically a determined
circle: any three of its distinct points form a noncollinear triple. -/
private noncomputable def determinedCircleOfSixTrace
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (htrace : (circleTrace cfg c).card = 6) :
    Erdos506.V1.DeterminedCircle cfg := by
  classical
  have hfull : circleTrace cfg c = (Finset.univ : Finset (Fin 6)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [htrace]
  have hc : ∀ i : Fin 6, cfg i ∈ (c.1 : Set Point2) := by
    intro i
    exact mem_circleTrace.mp (by simpa [hfull])
  let t : NoncollinearTriple cfg :=
    ⟨{0, 1, 2}, mem_noncollinearTriples.mpr ⟨by decide, by
      change ¬ Collinear ℝ (cfg '' (({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6)))
      have hset : cfg '' (({0, 1, 2} : Finset (Fin 6)) : Set (Fin 6)) =
          ({cfg 0, cfg 1, cfg 2} : Set Point2) := by
        ext x
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_insert,
          Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rcases hy with rfl | rfl | rfl <;> simp
        · intro hx
          rcases hx with hx | hx | hx
          · exact ⟨0, by simp, hx.symm⟩
          · exact ⟨1, by simp, hx.symm⟩
          · exact ⟨2, by simp, hx.symm⟩
      rw [hset]
      exact Erdos506.V3.not_collinear_three_distinct_on_sphere
        (hc 0) (hc 1) (hc 2) (cfg.injective.ne (by decide))
        (cfg.injective.ne (by decide)) (cfg.injective.ne (by decide))⟩⟩
  refine ⟨c, (mem_determinedCircles_iff cfg c).2 ⟨t, ?_⟩⟩
  intro x hx
  exact mem_circleTrace.mp (by simpa [hfull])

/-- Ungar's six-direction lower bound for six distinct points on one proper
circle.  The equality case has been reduced to the four dihedral chord
matchings above, so this theorem has no residual geometric hypothesis. -/
theorem six_le_card_determinedDirections_of_circleTrace_card_six
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (htrace : (circleTrace cfg c).card = 6) :
    6 ≤ (determinedDirections cfg).card := by
  let gamma := determinedCircleOfSixTrace cfg c htrace
  have hgamma : gamma.1 = c := rfl
  have hgammaTrace : (circleTrace cfg gamma.1).card = 6 := by
    simpa [hgamma] using htrace
  exact six_le_card_determinedDirections_of_determinedCircleTrace_card_six
    cfg gamma hgammaTrace

/-- For a labelled six-point circle, the finite part of Ungar is now
complete except for the all-perfect-matching equality case: it is enough to
find one direction represented by fewer than three chords. -/
theorem six_le_card_determinedDirections_of_circleTrace_card_six_of_nonperfect
    (cfg : Configuration (Fin 6)) (c : ProperCircle)
    (htrace : (circleTrace cfg c).card = 6)
    (hnonperfect : ∃ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 2) :
    6 ≤ (determinedDirections cfg).card := by
  apply six_le_card_determinedDirections_of_pair_class_cap_three cfg
  · intro D _
    exact directionPairClass_card_le_three_of_circleTrace_card_six cfg c htrace D
  · exact hnonperfect

/-- Consequently, a single non-perfect parallel class settles the full
six-direction lower bound.  This is the precise handoff from the geometric
circle argument to the finite rotating-line count. -/
theorem six_le_card_determinedDirections_of_circle_matching
    (cfg : Configuration (Fin 6))
    (hmatching : ∀ D ∈ determinedDirections cfg,
      DirectionClassIsMatching cfg D)
    (hnonperfect : ∃ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 2) :
    6 ≤ (determinedDirections cfg).card := by
  apply six_le_card_determinedDirections_of_pair_class_cap_three cfg
  · intro D hD
    exact directionPairClass_card_le_three_of_isMatching cfg D
      (hmatching D hD)
  · exact hnonperfect

end Erdos506.Incidence
