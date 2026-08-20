import Erdos506.Incidence.ProjectiveCompletion
import Erdos506.Incidence.RealProjectiveLineCyclicOrder
import Erdos506.Incidence.RealProjectiveLineSuccessor

/-!
# The scalar sign kernel behind projective triangle crossing

For four homogeneous line covectors `l,m,n,c`, intersecting the transversal
`c` with the three sides gives the raw vectors `l × c`, `m × c`, and
`n × c`.  The product of the two opposite-side evaluations at each of
these intersections is the homogeneous form of the corresponding
inside/outside arc test.  Their product is a negative square.  This is the
Menelaus parity identity needed by the canonical Felsner 5.8 sector router;
it contains no arrangement-specific or topological assumption.
-/

namespace Erdos506.Incidence

/-- Two nonzero real scalars have the same sign exactly when their product
is positive. -/
theorem sign_eq_sign_iff_mul_pos {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    SignType.sign x = SignType.sign y ↔ 0 < x * y := by
  rcases lt_or_gt_of_ne hx with hxNeg | hxPos <;>
    rcases lt_or_gt_of_ne hy with hyNeg | hyPos
  · rw [sign_eq_neg_one_iff.mpr hxNeg, sign_eq_neg_one_iff.mpr hyNeg]
    exact iff_of_true rfl (mul_pos_of_neg_of_neg hxNeg hyNeg)
  · rw [sign_eq_neg_one_iff.mpr hxNeg, sign_eq_one_iff.mpr hyPos]
    exact iff_of_false (by decide)
      (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hxNeg.le hyPos.le))
  · rw [sign_eq_one_iff.mpr hxPos, sign_eq_neg_one_iff.mpr hyNeg]
    exact iff_of_false (by decide)
      (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hxPos.le hyNeg.le))
  · rw [sign_eq_one_iff.mpr hxPos, sign_eq_one_iff.mpr hyPos]
    exact iff_of_true rfl (mul_pos hxPos hyPos)

/-- Public two-dimensional Cramer identity.  Applying a linear functional
to this vector equality is the clean way to compare a side evaluation with
the intrinsic bracket coordinate on that side. -/
theorem realProjectiveBracket_cramer_linear
    (p q r : RealProjectiveLineVector) :
    realProjectiveBracket q r • p + realProjectiveBracket p q • r =
      realProjectiveBracket p r • q := by
  ext i
  fin_cases i <;> simp [realProjectiveBracket] <;> ring

/-- A linear functional vanishing at `p` is, up to one fixed scalar, the
bracket coordinate with endpoint `p`. -/
theorem linearMap_apply_mul_realProjectiveBracket_eq
    (f : RealProjectiveLineVector →ₗ[ℝ] ℝ)
    (p q r : RealProjectiveLineVector) (hp : f p = 0) :
    f q * realProjectiveBracket p r =
      f r * realProjectiveBracket p q := by
  have h := congrArg f (realProjectiveBracket_cramer_linear p q r)
  simp only [map_add, map_smul, smul_eq_mul, hp, mul_zero, zero_add] at h
  simpa only [mul_comm] using h.symm

/-- Product of two endpoint-vanishing linear coordinates on `RP¹`. -/
def realProjectiveFunctionalPairProduct
    (f g : RealProjectiveLineVector →ₗ[ℝ] ℝ)
    (u : RealProjectiveLineVector) : ℝ :=
  f u * g u

/-- Exact comparison between a two-functional side test and the intrinsic
triple bracket.  The proportionality factor is independent of the moving
point `u`; this is what allows sign comparisons without choosing an affine
chart on the projective line. -/
theorem functionalPairProduct_mul_bracket_cube
    (f g : RealProjectiveLineVector →ₗ[ℝ] ℝ)
    (p r u : RealProjectiveLineVector)
    (hfp : f p = 0) (hgr : g r = 0) :
    realProjectiveFunctionalPairProduct f g u *
        realProjectiveBracket p r ^ 3 =
      -(f r * g p) * realProjectiveTripleBracket p u r := by
  have hfu :=
    linearMap_apply_mul_realProjectiveBracket_eq f p u r hfp
  have hgu₀ :=
    linearMap_apply_mul_realProjectiveBracket_eq g r u p hgr
  have hgu : g u * realProjectiveBracket p r =
      g p * realProjectiveBracket u r := by
    calc
      g u * realProjectiveBracket p r =
          -(g u * realProjectiveBracket r p) := by
        rw [realProjectiveBracket_swap p r]
        ring
      _ = -(g p * realProjectiveBracket r u) := by rw [hgu₀]
      _ = g p * realProjectiveBracket u r := by
        rw [realProjectiveBracket_swap u r]
        ring
  calc
    realProjectiveFunctionalPairProduct f g u *
          realProjectiveBracket p r ^ 3 =
        (f u * realProjectiveBracket p r) *
          (g u * realProjectiveBracket p r) *
            realProjectiveBracket p r := by
      simp only [realProjectiveFunctionalPairProduct]
      ring
    _ = (f r * realProjectiveBracket p u) *
          (g p * realProjectiveBracket u r) *
            realProjectiveBracket p r := by rw [hfu, hgu]
    _ = -(f r * g p) * realProjectiveTripleBracket p u r := by
      rw [realProjectiveTripleBracket,
        realProjectiveBracket_swap p r]
      ring

/-- The proportionality factor disappears after comparing two moving
points.  Consequently the side-product signs agree exactly when their
intrinsic cyclic triple-bracket signs agree. -/
theorem functionalPairProduct_mul_functionalPairProduct_pos_iff
    (f g : RealProjectiveLineVector →ₗ[ℝ] ℝ)
    (p r u v : RealProjectiveLineVector)
    (hfp : f p = 0) (hgr : g r = 0)
    (hpr : realProjectiveBracket p r ≠ 0)
    (hfr : f r ≠ 0) (hgp : g p ≠ 0) :
    0 < realProjectiveFunctionalPairProduct f g u *
        realProjectiveFunctionalPairProduct f g v ↔
      0 < realProjectiveTripleBracket p u r *
        realProjectiveTripleBracket p v r := by
  have hu := functionalPairProduct_mul_bracket_cube f g p r u hfp hgr
  have hv := functionalPairProduct_mul_bracket_cube f g p r v hfp hgr
  have hcompare :
      (realProjectiveFunctionalPairProduct f g u *
          realProjectiveFunctionalPairProduct f g v) *
          realProjectiveBracket p r ^ 6 =
        (f r * g p) ^ 2 *
          (realProjectiveTripleBracket p u r *
            realProjectiveTripleBracket p v r) := by
    calc
      (realProjectiveFunctionalPairProduct f g u *
          realProjectiveFunctionalPairProduct f g v) *
          realProjectiveBracket p r ^ 6 =
        (realProjectiveFunctionalPairProduct f g u *
            realProjectiveBracket p r ^ 3) *
          (realProjectiveFunctionalPairProduct f g v *
            realProjectiveBracket p r ^ 3) := by ring
      _ = (-(f r * g p) * realProjectiveTripleBracket p u r) *
          (-(f r * g p) * realProjectiveTripleBracket p v r) := by
        rw [hu, hv]
      _ = (f r * g p) ^ 2 *
          (realProjectiveTripleBracket p u r *
            realProjectiveTripleBracket p v r) := by ring
  have hbracketPos : 0 < realProjectiveBracket p r ^ 6 := by
    have hsq : 0 < (realProjectiveBracket p r ^ 3) ^ 2 :=
      sq_pos_of_ne_zero (pow_ne_zero 3 hpr)
    convert hsq using 1 <;> ring
  have hfactorPos : 0 < (f r * g p) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero hfr hgp)
  constructor
  · intro hpair
    have hleft : 0 <
        (realProjectiveFunctionalPairProduct f g u *
          realProjectiveFunctionalPairProduct f g v) *
            realProjectiveBracket p r ^ 6 :=
      mul_pos hpair hbracketPos
    rw [hcompare] at hleft
    exact (mul_pos_iff_of_pos_left hfactorPos).mp hleft
  · intro htriple
    have hright : 0 < (f r * g p) ^ 2 *
        (realProjectiveTripleBracket p u r *
          realProjectiveTripleBracket p v r) :=
      mul_pos hfactorPos htriple
    rw [← hcompare] at hright
    exact (mul_pos_iff_of_pos_right hbracketPos).mp hright

/-- Two points of `RP¹` lie in the same component cut out by `P,R`
exactly when their two oriented triple brackets have positive product. -/
theorem tripleBrackets_mul_pos_iff_cyclic_iff
    (P U V R : RealProjectiveOnePoint)
    (hU : realProjectiveTripleBracket P.rep U.rep R.rep ≠ 0)
    (hV : realProjectiveTripleBracket P.rep V.rep R.rep ≠ 0) :
    0 < realProjectiveTripleBracket P.rep U.rep R.rep *
          realProjectiveTripleBracket P.rep V.rep R.rep ↔
      (RealProjectiveCyclic P U R ↔ RealProjectiveCyclic P V R) := by
  have hcyU : RealProjectiveCyclic P U R ↔
      0 < realProjectiveTripleBracket P.rep U.rep R.rep :=
    realProjectiveCyclic_iff_rep_tripleBracket P U R
  have hcyV : RealProjectiveCyclic P V R ↔
      0 < realProjectiveTripleBracket P.rep V.rep R.rep :=
    realProjectiveCyclic_iff_rep_tripleBracket P V R
  rcases lt_or_gt_of_ne hU with hUn | hUp <;>
    rcases lt_or_gt_of_ne hV with hVn | hVp
  · exact iff_of_true (mul_pos_of_neg_of_neg hUn hVn)
      (iff_of_false (not_lt_of_ge hUn.le ∘ hcyU.mp)
        (not_lt_of_ge hVn.le ∘ hcyV.mp))
  · exact iff_of_false (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
        hUn.le hVp.le))
      (fun hiff => (not_lt_of_ge hUn.le ∘ hcyU.mp)
        (hiff.mpr (hcyV.mpr hVp)))
  · exact iff_of_false (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
        hUp.le hVn.le))
      (fun hiff => (not_lt_of_ge hVn.le ∘ hcyV.mp)
        (hiff.mp (hcyU.mpr hUp)))
  · exact iff_of_true (mul_pos hUp hVp)
      (iff_of_true (hcyU.mpr hUp) (hcyV.mpr hVp))

/-- Functional form of the same component classifier. -/
theorem functionalPairProduct_mul_pos_iff_cyclic_iff
    (f g : RealProjectiveLineVector →ₗ[ℝ] ℝ)
    (P R U V : RealProjectiveOnePoint)
    (hfp : f P.rep = 0) (hgr : g R.rep = 0)
    (hpr : realProjectiveBracket P.rep R.rep ≠ 0)
    (hfr : f R.rep ≠ 0) (hgp : g P.rep ≠ 0)
    (hU : realProjectiveTripleBracket P.rep U.rep R.rep ≠ 0)
    (hV : realProjectiveTripleBracket P.rep V.rep R.rep ≠ 0) :
    0 < realProjectiveFunctionalPairProduct f g U.rep *
          realProjectiveFunctionalPairProduct f g V.rep ↔
      (RealProjectiveCyclic P U R ↔ RealProjectiveCyclic P V R) := by
  exact (functionalPairProduct_mul_functionalPairProduct_pos_iff
    f g P.rep R.rep U.rep V.rep hfp hgr hpr hfr hgp).trans
      (tripleBrackets_mul_pos_iff_cyclic_iff P U V R hU hV)

/-- The raw two-side evaluation product at the intersection of `side` and
the transversal `c`.  Its sign distinguishes the two open arcs of `side`
cut out by `other₀` and `other₁`. -/
def triangleCrossingSideProduct
    (side other₀ other₁ c : Homogeneous3) : ℝ :=
  (crossProduct side c ⬝ᵥ other₀) *
    (crossProduct side c ⬝ᵥ other₁)

/-- The canonical representative of a projective cross is a nonzero scalar
multiple of the raw cross product of the canonical input representatives. -/
theorem projectiveCross_rep_eq_smul_crossProduct_reps
    (L M : RealProjectivePoint) (hLM : L ≠ M) :
    ∃ a : ℝ, a ≠ 0 ∧
      a • crossProduct L.rep M.rep = (Projectivization.cross L M).rep := by
  have hmkNe :
      Projectivization.mk ℝ L.rep L.rep_nonzero ≠
        Projectivization.mk ℝ M.rep M.rep_nonzero := by
    simpa only [L.mk_rep, M.mk_rep] using hLM
  have hraw : crossProduct L.rep M.rep ≠ 0 :=
    mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      L.rep_nonzero M.rep_nonzero).mpr hmkNe
  have hcross : Projectivization.cross L M =
      Projectivization.mk ℝ (crossProduct L.rep M.rep) hraw := by
    simpa only [L.mk_rep, M.mk_rep] using
      (Projectivization.cross_mk_of_ne
        L.rep_nonzero M.rep_nonzero hmkNe)
  have hproj :
      Projectivization.mk ℝ (Projectivization.cross L M).rep
          (Projectivization.cross L M).rep_nonzero =
        Projectivization.mk ℝ (crossProduct L.rep M.rep) hraw :=
    (Projectivization.cross L M).mk_rep.trans hcross
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    (Projectivization.cross L M).rep (crossProduct L.rep M.rep)
    (Projectivization.cross L M).rep_nonzero hraw).mp hproj
  have ha0 : a ≠ 0 := by
    intro ha0
    apply (Projectivization.cross L M).rep_nonzero
    rw [← ha, ha0, zero_smul]
  exact ⟨a, ha0, ha⟩

/-- Replacing a raw side intersection by Mathlib's canonical projective
representative multiplies its two-side test by a positive square. -/
theorem projectiveCross_pairEvaluation_eq_posSq_mul
    (L M N O : RealProjectivePoint) (hLM : L ≠ M) :
    ∃ a : ℝ, 0 < a ^ 2 ∧
      (((Projectivization.cross L M).rep ⬝ᵥ N.rep) *
          ((Projectivization.cross L M).rep ⬝ᵥ O.rep)) =
        a ^ 2 * triangleCrossingSideProduct L.rep N.rep O.rep M.rep := by
  obtain ⟨a, ha0, ha⟩ :=
    projectiveCross_rep_eq_smul_crossProduct_reps L M hLM
  refine ⟨a, sq_pos_of_ne_zero ha0, ?_⟩
  rw [← ha]
  simp only [triangleCrossingSideProduct, smul_dotProduct, smul_eq_mul]
  ring

/-- Vanishing of one evaluation at a projective cross can be checked on
the raw cross product of the input representatives. -/
theorem projectiveCross_evaluation_ne_zero_iff
    (L M N : RealProjectivePoint) (hLM : L ≠ M) :
    (Projectivization.cross L M).rep ⬝ᵥ N.rep ≠ 0 ↔
      crossProduct L.rep M.rep ⬝ᵥ N.rep ≠ 0 := by
  obtain ⟨a, ha0, ha⟩ :=
    projectiveCross_rep_eq_smul_crossProduct_reps L M hLM
  rw [← ha]
  simpa only [smul_dotProduct, smul_eq_mul] using
    (mul_ne_zero_iff_left ha0)

/-- In particular the positive sign of the two-side test is intrinsic. -/
theorem projectiveCross_pairEvaluation_pos_iff
    (L M N O : RealProjectivePoint) (hLM : L ≠ M) :
    0 < ((Projectivization.cross L M).rep ⬝ᵥ N.rep) *
          ((Projectivization.cross L M).rep ⬝ᵥ O.rep) ↔
      0 < triangleCrossingSideProduct L.rep N.rep O.rep M.rep := by
  obtain ⟨a, ha, heq⟩ :=
    projectiveCross_pairEvaluation_eq_posSq_mul L M N O hLM
  rw [heq]
  exact mul_pos_iff_of_pos_left ha

/-- The negative sign of the same test is intrinsic as well. -/
theorem projectiveCross_pairEvaluation_neg_iff
    (L M N O : RealProjectivePoint) (hLM : L ≠ M) :
    ((Projectivization.cross L M).rep ⬝ᵥ N.rep) *
          ((Projectivization.cross L M).rep ⬝ᵥ O.rep) < 0 ↔
      triangleCrossingSideProduct L.rep N.rep O.rep M.rep < 0 := by
  obtain ⟨a, ha, heq⟩ :=
    projectiveCross_pairEvaluation_eq_posSq_mul L M N O hLM
  rw [heq]
  constructor
  · intro hneg
    rcases mul_neg_iff.mp hneg with h | h
    · exact h.2
    · exact False.elim (not_lt_of_ge ha.le h.1)
  · intro hneg
    exact mul_neg_iff.mpr (Or.inl ⟨ha, hneg⟩)

/-- Homogeneous Menelaus parity for a line crossing the three sides of a
projective triangle. -/
theorem triangleCrossing_sideProducts_mul_eq_neg_sq
    (l m n c : Homogeneous3) :
    (((crossProduct l c ⬝ᵥ m) * (crossProduct l c ⬝ᵥ n)) *
        ((crossProduct m c ⬝ᵥ l) * (crossProduct m c ⬝ᵥ n))) *
        ((crossProduct n c ⬝ᵥ l) * (crossProduct n c ⬝ᵥ m)) =
      -((c ⬝ᵥ crossProduct m n) *
          (c ⬝ᵥ crossProduct n l) *
          (c ⬝ᵥ crossProduct l m)) ^ 2 := by
  have hlcm : crossProduct l c ⬝ᵥ m =
      -(c ⬝ᵥ crossProduct l m) := by
    calc
      crossProduct l c ⬝ᵥ m = m ⬝ᵥ crossProduct l c :=
        dotProduct_comm _ _
      _ = l ⬝ᵥ crossProduct c m := triple_product_permutation _ _ _
      _ = c ⬝ᵥ crossProduct m l := triple_product_permutation _ _ _
      _ = c ⬝ᵥ (-crossProduct l m) :=
        congrArg (fun v => c ⬝ᵥ v) (cross_anticomm l m).symm
      _ = -(c ⬝ᵥ crossProduct l m) :=
        dotProduct_neg c (crossProduct l m)
  have hlcn : crossProduct l c ⬝ᵥ n =
      c ⬝ᵥ crossProduct n l := by
    calc
      crossProduct l c ⬝ᵥ n = n ⬝ᵥ crossProduct l c :=
        dotProduct_comm _ _
      _ = l ⬝ᵥ crossProduct c n := triple_product_permutation _ _ _
      _ = c ⬝ᵥ crossProduct n l := triple_product_permutation _ _ _
  have hmcl : crossProduct m c ⬝ᵥ l =
      c ⬝ᵥ crossProduct l m := by
    calc
      crossProduct m c ⬝ᵥ l = l ⬝ᵥ crossProduct m c :=
        dotProduct_comm _ _
      _ = m ⬝ᵥ crossProduct c l := triple_product_permutation _ _ _
      _ = c ⬝ᵥ crossProduct l m := triple_product_permutation _ _ _
  have hmcn : crossProduct m c ⬝ᵥ n =
      -(c ⬝ᵥ crossProduct m n) := by
    calc
      crossProduct m c ⬝ᵥ n = n ⬝ᵥ crossProduct m c :=
        dotProduct_comm _ _
      _ = m ⬝ᵥ crossProduct c n := triple_product_permutation _ _ _
      _ = c ⬝ᵥ crossProduct n m := triple_product_permutation _ _ _
      _ = c ⬝ᵥ (-crossProduct m n) :=
        congrArg (fun v => c ⬝ᵥ v) (cross_anticomm m n).symm
      _ = -(c ⬝ᵥ crossProduct m n) :=
        dotProduct_neg c (crossProduct m n)
  have hncl : crossProduct n c ⬝ᵥ l =
      -(c ⬝ᵥ crossProduct n l) := by
    calc
      crossProduct n c ⬝ᵥ l = l ⬝ᵥ crossProduct n c :=
        dotProduct_comm _ _
      _ = n ⬝ᵥ crossProduct c l := triple_product_permutation _ _ _
      _ = c ⬝ᵥ crossProduct l n := triple_product_permutation _ _ _
      _ = c ⬝ᵥ (-crossProduct n l) :=
        congrArg (fun v => c ⬝ᵥ v) (cross_anticomm n l).symm
      _ = -(c ⬝ᵥ crossProduct n l) :=
        dotProduct_neg c (crossProduct n l)
  have hncm : crossProduct n c ⬝ᵥ m =
      c ⬝ᵥ crossProduct m n := by
    calc
      crossProduct n c ⬝ᵥ m = m ⬝ᵥ crossProduct n c :=
        dotProduct_comm _ _
      _ = n ⬝ᵥ crossProduct c m := triple_product_permutation _ _ _
      _ = c ⬝ᵥ crossProduct m n := triple_product_permutation _ _ _
  rw [hlcm, hlcn, hmcl, hmcn, hncl, hncm]
  ring

/-- Away from the three triangle vertices, the product of the three raw arc
tests is strictly negative. -/
theorem triangleCrossing_sideProducts_mul_neg
    (l m n c : Homogeneous3)
    (hmn : c ⬝ᵥ crossProduct m n ≠ 0)
    (hnl : c ⬝ᵥ crossProduct n l ≠ 0)
    (hlm : c ⬝ᵥ crossProduct l m ≠ 0) :
    (((crossProduct l c ⬝ᵥ m) * (crossProduct l c ⬝ᵥ n)) *
        ((crossProduct m c ⬝ᵥ l) * (crossProduct m c ⬝ᵥ n))) *
        ((crossProduct n c ⬝ᵥ l) * (crossProduct n c ⬝ᵥ m)) < 0 := by
  rw [triangleCrossing_sideProducts_mul_eq_neg_sq]
  exact neg_neg_of_pos (sq_pos_of_ne_zero
    (mul_ne_zero (mul_ne_zero hmn hnl) hlm))

/-- Menelaus sign dispatch: the third side test is negative exactly when
the product of the first two side tests is positive.  This is the
arrangement-free Boolean kernel used to route the two cyclic base intervals
to the two canonical sectors adjacent to a selected clean side. -/
theorem triangleCrossing_thirdSideProduct_neg_iff
    (l m n c : Homogeneous3)
    (hmn : c ⬝ᵥ crossProduct m n ≠ 0)
    (hnl : c ⬝ᵥ crossProduct n l ≠ 0)
    (hlm : c ⬝ᵥ crossProduct l m ≠ 0) :
    triangleCrossingSideProduct n l m c < 0 ↔
      0 < triangleCrossingSideProduct l m n c *
        triangleCrossingSideProduct m l n c := by
  have hneg := triangleCrossing_sideProducts_mul_neg l m n c hmn hnl hlm
  change
    ((triangleCrossingSideProduct l m n c *
        triangleCrossingSideProduct m l n c) *
      triangleCrossingSideProduct n l m c < 0) at hneg
  rcases mul_neg_iff.mp hneg with h | h
  · exact iff_of_true h.2 h.1
  · exact iff_of_false (not_lt_of_ge h.2.le) (not_lt_of_ge h.1.le)

/-- Symmetric positive form of the same sign dispatch. -/
theorem triangleCrossing_thirdSideProduct_pos_iff
    (l m n c : Homogeneous3)
    (hmn : c ⬝ᵥ crossProduct m n ≠ 0)
    (hnl : c ⬝ᵥ crossProduct n l ≠ 0)
    (hlm : c ⬝ᵥ crossProduct l m ≠ 0) :
    0 < triangleCrossingSideProduct n l m c ↔
      triangleCrossingSideProduct l m n c *
          triangleCrossingSideProduct m l n c < 0 := by
  have hneg := triangleCrossing_sideProducts_mul_neg l m n c hmn hnl hlm
  change
    ((triangleCrossingSideProduct l m n c *
        triangleCrossingSideProduct m l n c) *
      triangleCrossingSideProduct n l m c < 0) at hneg
  rcases mul_neg_iff.mp hneg with h | h
  · exact iff_of_false (not_lt_of_ge h.2.le) (not_lt_of_ge h.1.le)
  · exact iff_of_true h.2 h.1

end Erdos506.Incidence
