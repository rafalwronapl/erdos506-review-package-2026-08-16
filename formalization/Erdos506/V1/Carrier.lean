import Erdos506.Block.System
import Erdos506.Incidence.SpannedLines
import Erdos506.V1.Model

/-!
# Full line and circle carriers for V1

Every selected pair determines one full affine-line trace.  Every selected
noncollinear triple determines one full proper-circle trace, while a collinear
triple belongs to its line trace.  This file builds these semantic objects and
proves the geometric uniqueness needed by the abstract block system.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

/-- A V1 generalized carrier is either a selected-point-spanned line or a
proper circle determined by a noncollinear selected triple. -/
abbrev GeometricBlock {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :=
  DeterminedLine cfg ⊕ DeterminedCircle cfg

def geometricBlockKind {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} : GeometricBlock cfg → BlockKind
  | .inl _ => .line
  | .inr _ => .circle

noncomputable def geometricBlockSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : GeometricBlock cfg → Finset α
  | .inl L => lineSupport cfg L
  | .inr c => circleTrace cfg c.1

/-- A canonical two-subset inside a three-subset. -/
noncomputable def pairInsideTriple
    {α : Type*} [Fintype α] [DecidableEq α] (A : KSubset α 3) :
    {B : KSubset α 2 // B.1 ⊆ A.1} := by
  classical
  have htwo : 2 ≤ A.1.card := by omega
  let B := Classical.choose (Finset.exists_subset_card_eq htwo)
  have hBspec := Classical.choose_spec (Finset.exists_subset_card_eq htwo)
  exact ⟨⟨B, hBspec.2⟩, hBspec.1⟩

/-- The determined line carried by the chosen pair inside a triple. -/
noncomputable def lineOfTriple
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3) : DeterminedLine cfg :=
  ⟨lineOfPair cfg (pairInsideTriple A).1,
    lineOfPair_mem_determinedLines cfg (pairInsideTriple A).1⟩

/-- A noncollinear three-support, bundled for the circumcircle API. -/
def attachedNoncollinearTriple
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3)
    (hA : IsNoncollinear cfg A.1) : NoncollinearTriple cfg :=
  ⟨A.1, mem_noncollinearTriples.mpr ⟨A.2, hA⟩⟩

/-- The determined circle carried by a noncollinear three-support. -/
noncomputable def circleOfTriple
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3)
    (hA : IsNoncollinear cfg A.1) : DeterminedCircle cfg := by
  let t := attachedNoncollinearTriple cfg A hA
  refine ⟨properCircumcircle cfg t, ?_⟩
  apply (mem_determinedCircles_iff cfg (properCircumcircle cfg t)).2
  exact ⟨t, fun x hx => support_mem_properCircumcircle cfg t hx⟩

theorem triple_subset_circleOfTriple
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3)
    (hA : IsNoncollinear cfg A.1) :
    A.1 ⊆ circleTrace cfg (circleOfTriple cfg A hA).1 := by
  intro x hx
  apply mem_circleTrace.mpr
  exact support_mem_properCircumcircle cfg
    (attachedNoncollinearTriple cfg A hA) hx

/-- If a selected triple is collinear, every one of its labels lies on the
line spanned by the chosen internal pair. -/
theorem triple_subset_lineOfTriple_of_collinear
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3)
    (hA : ¬IsNoncollinear cfg A.1) :
    A.1 ⊆ lineSupport cfg (lineOfTriple cfg A) := by
  classical
  have hcol : Collinear ℝ (supportPoints cfg A.1) := by
    simpa [IsNoncollinear] using hA
  let B : KSubset α 2 := (pairInsideTriple A).1
  have hBA : B.1 ⊆ A.1 := (pairInsideTriple A).2
  obtain ⟨a, b, hab, hB⟩ := Finset.card_eq_two.mp B.2
  have haA : a ∈ A.1 := hBA (by simp [hB])
  have hbA : b ∈ A.1 := hBA (by simp [hB])
  have haS : cfg a ∈ supportPoints cfg A.1 := ⟨a, haA, rfl⟩
  have hbS : cfg b ∈ supportPoints cfg A.1 := ⟨b, hbA, rfl⟩
  have habCfg : cfg a ≠ cfg b := cfg.injective.ne hab
  have hline : lineOfPair cfg B = affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
    unfold lineOfPair
    rw [hB]
    congr 1
    ext y
    simp [eq_comm]
  intro x hx
  rw [mem_lineSupport]
  change cfg x ∈ lineOfPair cfg B
  rw [hline]
  exact hcol.mem_affineSpan_of_mem_of_ne haS hbS ⟨x, hx, rfl⟩ habCfg

/-- A noncollinear selected triple cannot be contained in a determined line. -/
theorem not_triple_subset_line_of_noncollinear
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3)
    (hA : IsNoncollinear cfg A.1) (L : DeterminedLine cfg) :
    ¬A.1 ⊆ lineSupport cfg L := by
  classical
  intro hsub
  obtain ⟨a, b, c, hab, hac, hbc, hAeq⟩ := Finset.card_eq_three.mp A.2
  have haL : cfg a ∈ L.1 := mem_lineSupport.mp (hsub (by simp [hAeq]))
  have hbL : cfg b ∈ L.1 := mem_lineSupport.mp (hsub (by simp [hAeq]))
  have hcL : cfg c ∈ L.1 := mem_lineSupport.mp (hsub (by simp [hAeq]))
  obtain ⟨D, hDL⟩ := L.exists_pair
  obtain ⟨u, v, huv, hD⟩ := Finset.card_eq_two.mp D.2
  have hline : lineOfPair cfg D = affineSpan ℝ ({cfg u, cfg v} : Set Point2) := by
    unfold lineOfPair
    rw [hD]
    congr 1
    ext y
    simp [eq_comm]
  have hLline : L.1 = affineSpan ℝ ({cfg u, cfg v} : Set Point2) := by
    rw [← hline, hDL]
  rw [hLline] at haL hbL hcL
  have hcol : Collinear ℝ ({cfg a, cfg b, cfg c} : Set Point2) :=
    collinear_triple_of_mem_affineSpan_pair haL hbL hcL
  have hsupp : supportPoints cfg A.1 =
      ({cfg a, cfg b, cfg c} : Set Point2) := by
    rw [hAeq]
    ext y
    simp [supportPoints, eq_comm]
  exact hA (hsupp.symm ▸ hcol)

/-- Three distinct collinear selected points cannot all lie on a proper
circle. -/
theorem not_triple_subset_circle_of_collinear
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3)
    (hA : ¬IsNoncollinear cfg A.1) (c : ProperCircle) :
    ¬A.1 ⊆ circleTrace cfg c := by
  classical
  intro hsub
  obtain ⟨a, b, d, hab, had, hbd, hAeq⟩ := Finset.card_eq_three.mp A.2
  have haA : a ∈ A.1 := by simp [hAeq]
  have hbA : b ∈ A.1 := by simp [hAeq]
  have hdA : d ∈ A.1 := by simp [hAeq]
  have haC := mem_circleTrace.mp (hsub haA)
  have hbC := mem_circleTrace.mp (hsub hbA)
  have hdC := mem_circleTrace.mp (hsub hdA)
  have hind : AffineIndependent ℝ ![cfg a, cfg b, cfg d] :=
    (EuclideanGeometry.Sphere.cospherical c.1).affineIndependent_of_mem_of_ne
      haC hbC hdC (cfg.injective.ne hab) (cfg.injective.ne had)
        (cfg.injective.ne hbd)
  have hnotcol : ¬Collinear ℝ ({cfg a, cfg b, cfg d} : Set Point2) :=
    affineIndependent_iff_not_collinear_set.mp hind
  have hsupp : supportPoints cfg A.1 =
      ({cfg a, cfg b, cfg d} : Set Point2) := by
    rw [hAeq]
    ext y
    simp [supportPoints, eq_comm]
  have hcol : Collinear ℝ (supportPoints cfg A.1) := by
    simpa [IsNoncollinear] using hA
  exact hnotcol (hsupp ▸ hcol)

/-- The geometric owner of a selected triple: its circumcircle in the
noncollinear case, and the line through a fixed internal pair otherwise. -/
noncomputable def geometricTripleOwner
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3) : GeometricBlock cfg := by
  classical
  exact if hA : IsNoncollinear cfg A.1 then
    .inr (circleOfTriple cfg A hA)
  else
    .inl (lineOfTriple cfg A)

theorem geometricTripleOwner_contains
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3) :
    A.1 ⊆ geometricBlockSupport cfg (geometricTripleOwner cfg A) := by
  classical
  simp only [geometricTripleOwner]
  split
  · exact triple_subset_circleOfTriple cfg A ‹IsNoncollinear cfg A.1›
  · exact triple_subset_lineOfTriple_of_collinear cfg A
      ‹¬IsNoncollinear cfg A.1›

/-- No second generalized carrier can contain all three labels of a selected
triple. -/
theorem geometricTripleOwner_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 3) (b : GeometricBlock cfg)
    (hsub : A.1 ⊆ geometricBlockSupport cfg b) :
    b = geometricTripleOwner cfg A := by
  classical
  cases b with
  | inl L =>
      by_cases hA : IsNoncollinear cfg A.1
      · exact (not_triple_subset_line_of_noncollinear cfg A hA L hsub).elim
      · rw [geometricTripleOwner, dif_neg hA]
        have hL : L = lineOfTriple cfg A := by
          apply Subtype.ext
          let B : KSubset α 2 := (pairInsideTriple A).1
          have hline : lineOfPair cfg B = L.1 :=
            lineOfPair_eq_of_mem_of_direction_finrank_one cfg B L.1
              (by
                intro x hx
                apply mem_lineSupport.mp
                exact hsub ((pairInsideTriple A).2 hx))
              L.direction_finrank
          exact hline.symm
        exact congrArg (Sum.inl : DeterminedLine cfg → GeometricBlock cfg) hL
  | inr c =>
      by_cases hA : IsNoncollinear cfg A.1
      · rw [geometricTripleOwner, dif_pos hA]
        have hc : c = circleOfTriple cfg A hA := by
          apply Subtype.ext
          exact properCircle_eq_properCircumcircle_of_support cfg
            (attachedNoncollinearTriple cfg A hA) c.1
            (by
              intro x hx
              exact mem_circleTrace.mp (hsub hx))
        exact congrArg (Sum.inr : DeterminedCircle cfg → GeometricBlock cfg) hc
      · exact (not_triple_subset_circle_of_collinear cfg A hA c.1 hsub).elim

/-- The line carrier owned by an unordered pair. -/
noncomputable def geometricLineOwner
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 2) :
    {b : GeometricBlock cfg // geometricBlockKind b = .line} :=
  ⟨.inl ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩, rfl⟩

theorem geometricLineOwner_contains
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 2) :
    A.1 ⊆ geometricBlockSupport cfg (geometricLineOwner cfg A).1 :=
  pair_subset_lineSupport cfg A

theorem geometricLineOwner_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 2)
    (b : {b : GeometricBlock cfg // geometricBlockKind b = .line})
    (hsub : A.1 ⊆ geometricBlockSupport cfg b.1) :
    b = geometricLineOwner cfg A := by
  classical
  rcases b with ⟨b, hb⟩
  cases b with
  | inl L =>
      apply Subtype.ext
      let LA : DeterminedLine cfg :=
        ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
      have hL : L = LA := by
        apply Subtype.ext
        exact (lineOfPair_eq_of_mem_of_direction_finrank_one cfg A L.1
          (by
            intro x hx
            exact mem_lineSupport.mp (hsub hx))
          L.direction_finrank).symm
      simpa [geometricLineOwner, LA] using
        congrArg (Sum.inl : DeterminedLine cfg → GeometricBlock cfg) hL
  | inr c =>
      cases hb

/-- The concrete V1 line/circle carrier satisfies the abstract block-system
interface.  In particular, all pair and triple partition identities are now
available without enumerating configurations. -/
noncomputable def geometricBlockSystem
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : BlockSystem α (GeometricBlock cfg) where
  kind := geometricBlockKind
  support := geometricBlockSupport cfg
  line_min := by
    intro b hb
    cases b with
    | inl L => exact two_le_lineSupport_card cfg L
    | inr c => cases hb
  circle_min := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact Erdos506.V3.circleSupport_card_ge_three cfg c
  tripleOwner := geometricTripleOwner cfg
  triple_contains := geometricTripleOwner_contains cfg
  triple_unique := geometricTripleOwner_unique cfg
  lineOwner := geometricLineOwner cfg
  line_contains := geometricLineOwner_contains cfg
  line_owner_unique := geometricLineOwner_unique cfg

end Erdos506.V1
