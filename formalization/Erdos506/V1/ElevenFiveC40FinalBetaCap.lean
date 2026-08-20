import Erdos506.V1.ElevenFiveC40FinalSevenDefectRow
import Erdos506.V1.TenFiveSixPower

/-!
# The C40 pivot-inversion beta cap

This file supplies the missing geometric direction in the C40 `L = 11`
seven-defect row.  Inverting away from a pivot gives a ten-point
configuration.  A proper circle of that configuration pulls back either to
a proper circle away from the pivot or, when it contains the inversion
centre, to a line.  The five-block cap rules out a full pulled-back trace.

The first batch records this admissibility bridge.  The subsequent finite
map from its determined circles to away generalized blocks yields the sharp
beta cap.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace
open scoped BigOperators EuclideanSpace

universe u

/-- Pull a point of an inverted proper circle back through the pivot
inversion. -/
theorem pivotInversion_preimage_mem_invertedProperCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (c : ProperCircle)
    (hc : cfg p ∉ (c.1 : Set Point2)) (q : AwayFrom p)
    (hq : pivotInversion cfg p q ∈ (c.1 : Set Point2)) :
    cfg q.1 ∈
      ((invertedProperCircle (cfg p) c hc).1 : Set Point2) := by
  have hback := inversion_mem_invertedProperCircle
    (cfg p) (pivotInversion cfg p q) c hc hq
  simpa [pivotInversion, EuclideanGeometry.inversion_inversion] using hback

/-- If a proper circle of the inverted configuration contains the inversion
centre, its other points pull back to its perpendicular-bisector line. -/
theorem pivotInversion_preimage_mem_perpBisector_of_circle_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (c : ProperCircle)
    (hc : cfg p ∈ (c.1 : Set Point2)) (q : AwayFrom p)
    (hq : pivotInversion cfg p q ∈ (c.1 : Set Point2)) :
    cfg q.1 ∈ perpBisector (cfg p)
      (EuclideanGeometry.inversion (cfg p) 1 c.1.center) := by
  have hqne : pivotInversion cfg p q ≠ cfg p := by
    intro h
    have hqp : cfg q.1 = cfg p :=
      (EuclideanGeometry.inversion_eq_center one_ne_zero).mp (by
        simpa [pivotInversion] using h)
    exact q.2 (cfg.injective hqp)
  have hline :=
    (mem_circle_through_center_iff_inversion_mem_perpBisector
      (cfg p) (pivotInversion cfg p q) c hqne hc).mp hq
  simpa [pivotInversion, EuclideanGeometry.inversion_inversion] using hline

/-- Under the eleven-point five-block cap, no pivot inversion can put all
ten remaining labels on one proper circle.  The centre-on-circle and
centre-off-circle cases pull back respectively to a line and a circle of
the original configuration. -/
theorem pivotInversion_notConcyclic_of_blockSizeCap_five
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5) (p : Point) :
    NotConcyclic (pivotInversion cfg p) := by
  classical
  intro c
  have hle :
      (circleTrace (pivotInversion cfg p) c).card ≤
        Fintype.card (AwayFrom p) := by
    simpa using Finset.card_le_univ
      (circleTrace (pivotInversion cfg p) c)
  apply lt_of_le_of_ne hle
  intro heq
  have hall : circleTrace (pivotInversion cfg p) c = Finset.univ :=
    Finset.eq_univ_of_card _ heq
  let U : Finset Point :=
    liftAwayFinset (Finset.univ : Finset (AwayFrom p))
  have hUcard : U.card = 10 := by
    rw [show U.card = (Finset.univ : Finset (AwayFrom p)).card by
      exact card_liftAwayFinset _]
    simp [hcard]
  by_cases hc : cfg p ∈ (c.1 : Set Point2)
  · let P : AffineSubspace ℝ Point2 :=
      perpBisector (cfg p)
        (EuclideanGeometry.inversion (cfg p) 1 c.1.center)
    have hcenterNe : c.1.center ≠ cfg p :=
      properCircle_center_ne_of_mem (cfg p) c hc
    have hpinv : cfg p ≠
        EuclideanGeometry.inversion (cfg p) 1 c.1.center := by
      intro h
      apply hcenterNe
      exact (EuclideanGeometry.center_eq_inversion one_ne_zero).mp h
    have hPfin : Module.finrank ℝ P.direction = 1 := by
      dsimp [P]
      rw [direction_perpBisector]
      exact Submodule.finrank_orthogonal_span_singleton
        (sub_ne_zero.mpr hpinv.symm)
    have hUP : ∀ x ∈ U, cfg x ∈ P := by
      intro x hx
      obtain ⟨q, _hq, rfl⟩ := mem_liftAwayFinset.mp hx
      have hqCircle : q ∈ circleTrace (pivotInversion cfg p) c := by
        rw [hall]
        exact Finset.mem_univ q
      have hqGeom : pivotInversion cfg p q ∈ (c.1 : Set Point2) :=
        mem_circleTrace.mp hqCircle
      change cfg q.1 ∈ P
      simpa [P] using
        pivotInversion_preimage_mem_perpBisector_of_circle_mem
          cfg p c hc q hqGeom
    have hUtwo : 2 ≤ U.card := by omega
    obtain ⟨Aset, hAU, hAcard⟩ := Finset.exists_subset_card_eq hUtwo
    let A : KSubset Point 2 := ⟨Aset, hAcard⟩
    let L : DeterminedLine cfg :=
      ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
    have hpair : lineOfPair cfg A = P := by
      apply lineOfPair_eq_of_mem_of_direction_finrank_one cfg A P
      · intro x hx
        exact hUP x (hAU hx)
      · exact hPfin
    have hUsub : U ⊆ lineSupport cfg L := by
      intro x hx
      apply mem_lineSupport.mpr
      change cfg x ∈ lineOfPair cfg A
      rw [hpair]
      exact hUP x hx
    have hten : 10 ≤ (lineSupport cfg L).card := by
      rw [← hUcard]
      exact Finset.card_le_card hUsub
    have hfive : (lineSupport cfg L).card ≤ 5 := by
      have hthree : 3 ≤
          ((blockSystem cfg).support (Sum.inl L)).card := by
        simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
          (show 3 ≤ (lineSupport cfg L).card by omega)
      simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcap (Sum.inl L) hthree
    omega
  · let cBack : ProperCircle := invertedProperCircle (cfg p) c hc
    have hUsub : U ⊆ circleTrace cfg cBack := by
      intro x hx
      obtain ⟨q, _hq, rfl⟩ := mem_liftAwayFinset.mp hx
      have hqCircle : q ∈ circleTrace (pivotInversion cfg p) c := by
        rw [hall]
        exact Finset.mem_univ q
      have hqGeom : pivotInversion cfg p q ∈ (c.1 : Set Point2) :=
        mem_circleTrace.mp hqCircle
      apply mem_circleTrace.mpr
      simpa [cBack] using
        pivotInversion_preimage_mem_invertedProperCircle cfg p c hc q hqGeom
    have hUthree : 3 ≤ U.card := by omega
    obtain ⟨Aset, hAU, hAcard⟩ := Finset.exists_subset_card_eq hUthree
    let A : KSubset Point 3 := ⟨Aset, hAcard⟩
    have hAnoncol : IsNoncollinear cfg A.1 := by
      by_contra hcol
      exact not_triple_subset_circle_of_collinear cfg A hcol cBack
        (hAU.trans hUsub)
    let t : NoncollinearTriple cfg :=
      attachedNoncollinearTriple cfg A hAnoncol
    have hcBackDet : cBack ∈ determinedCircles cfg := by
      apply (mem_determinedCircles_iff cfg cBack).2
      refine ⟨t, ?_⟩
      intro x hx
      exact mem_circleTrace.mp (hAU.trans hUsub hx)
    let dc : DeterminedCircle cfg := ⟨cBack, hcBackDet⟩
    have hten : 10 ≤ (circleTrace cfg cBack).card := by
      rw [← hUcard]
      exact Finset.card_le_card hUsub
    have hfive : (circleTrace cfg cBack).card ≤ 5 := by
      have hthree : 3 ≤
          ((blockSystem cfg).support (Sum.inr dc)).card := by
        simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
          Erdos506.V3.circleSupport_card_ge_three cfg dc
      simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcap (Sum.inr dc) hthree
    omega

/-- The inverted ten-point configuration is admissible under the original
eleven-point five-block cap. -/
theorem pivotInversion_admissible_of_blockSizeCap_five
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5) (p : Point) :
    Admissible (pivotInversion cfg p) := by
  refine ⟨?_, pivotInversion_notConcyclic_of_blockSizeCap_five
    cfg hcard hcap p⟩
  exact pivotInversion_noncollinear cfg hadm (by omega) p

/-! ## Determined circles pull back to away block owners -/

/-- Choose the attached noncollinear triple witnessing a determined circle
of a pivot inversion. -/
noncomputable def pivotInversionCircleWitness
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) :
    NoncollinearTriple (pivotInversion cfg p) :=
  Classical.choose
    ((mem_determinedCircles_iff (pivotInversion cfg p) c.1).mp c.2)

/-- The selected witness triple lies on its determined circle. -/
theorem pivotInversionCircleWitness_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) :
    ∀ q ∈ (pivotInversionCircleWitness cfg p c).1,
      pivotInversion cfg p q ∈ (c.1 : Set Point2) := by
  simpa [pivotInversionCircleWitness] using
    Classical.choose_spec
      ((mem_determinedCircles_iff (pivotInversion cfg p) c.1).mp c.2)

/-- Forgetting the away-label proofs in the witness triple gives an actual
three-subset of the original labels. -/
noncomputable def pivotInversionCircleBackTriple
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) : KSubset Point 3 :=
  ⟨liftAwayFinset (pivotInversionCircleWitness cfg p c).1, by
    rw [card_liftAwayFinset]
    exact (mem_noncollinearTriples.mp
      (pivotInversionCircleWitness cfg p c).2).1⟩

/-- Each label of the inverted witness triple belongs to the lifted original
triple. -/
theorem pivotInversionCircleWitness_mem_backTriple
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p))
    (q : AwayFrom p) (hq : q ∈ (pivotInversionCircleWitness cfg p c).1) :
    q.1 ∈ (pivotInversionCircleBackTriple cfg p c).1 := by
  change q.1 ∈ liftAwayFinset (pivotInversionCircleWitness cfg p c).1
  exact mem_liftAwayFinset.mpr ⟨q, hq, rfl⟩

/-- The geometric owner of the lifted witness triple. -/
noncomputable def pivotInversionCircleBackBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) : GeometricBlock cfg :=
  geometricTripleOwner cfg (pivotInversionCircleBackTriple cfg p c)

/-- The pulled-back owner has at least three labels. -/
theorem three_le_pivotInversionCircleBackBlock_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) :
    3 ≤ (geometricBlockSupport cfg
      (pivotInversionCircleBackBlock cfg p c)).card := by
  let A := pivotInversionCircleBackTriple cfg p c
  have hsub : A.1 ⊆ geometricBlockSupport cfg
      (geometricTripleOwner cfg A) :=
    geometricTripleOwner_contains cfg A
  have hle := Finset.card_le_card hsub
  change 3 ≤ (geometricBlockSupport cfg
    (geometricTripleOwner cfg A)).card
  rw [← A.2]
  exact hle

/-- The owner of a pulled-back noncollinear inverted triple cannot contain
the inversion pivot: otherwise that triple would lie on the corresponding
inverted determined line. -/
theorem pivotInversionCircleBackBlock_away
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) :
    p ∉ geometricBlockSupport cfg
      (pivotInversionCircleBackBlock cfg p c) := by
  classical
  let A := pivotInversionCircleBackTriple cfg p c
  let b : GeometricBlock cfg := geometricTripleOwner cfg A
  let t := pivotInversionCircleWitness cfg p c
  let T : KSubset (AwayFrom p) 3 := ⟨t.1,
    (mem_noncollinearTriples.mp t.2).1⟩
  intro hp
  have hcard : 3 ≤ (geometricBlockSupport cfg b).card := by
    have hsub : A.1 ⊆ geometricBlockSupport cfg b := by
      simpa [b] using geometricTripleOwner_contains cfg A
    rw [← A.2]
    exact Finset.card_le_card hsub
  let pb : PivotBlock cfg p := ⟨b, by simpa [b] using hp, hcard⟩
  have hsub : T.1 ⊆ lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p pb) := by
    intro q hq
    have hqA : q.1 ∈ A.1 := by
      simpa [A, t, T] using
        pivotInversionCircleWitness_mem_backTriple cfg p c q hq
    have howner : q.1 ∈ geometricBlockSupport cfg b := by
      simpa [b] using (geometricTripleOwner_contains cfg A hqA)
    have haway : q ∈ awaySupport p (geometricBlockSupport cfg b) := by
      exact mem_awaySupport.mpr howner
    have hline : q ∈ lineSupport (pivotInversion cfg p)
        (blockToPivotLine cfg p pb) := by
      rw [lineSupport_blockToPivotLine cfg p pb]
      exact haway
    exact hline
  have hnoncol : IsNoncollinear (pivotInversion cfg p) T.1 := by
    simpa [T, t] using (mem_noncollinearTriples.mp t.2).2
  exact (not_triple_subset_line_of_noncollinear
    (pivotInversion cfg p) T hnoncol (blockToPivotLine cfg p pb) hsub)

/-- Inverting the away owner of the lifted witness triple recovers the
original determined circle of the pivot inversion. -/
theorem pivotInversionCircleBackBlock_inverted_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (c : DeterminedCircle (pivotInversion cfg p)) :
    c.1 = invertedAwayGeometricBlockCircle cfg p
      (pivotInversionCircleBackBlock cfg p c)
      (pivotInversionCircleBackBlock_away cfg p c) := by
  classical
  let A := pivotInversionCircleBackTriple cfg p c
  let b : GeometricBlock cfg := geometricTripleOwner cfg A
  let t := pivotInversionCircleWitness cfg p c
  have hcEq : c.1 = properCircumcircle (pivotInversion cfg p) t := by
    apply properCircle_eq_properCircumcircle_of_support
      (pivotInversion cfg p) t c.1
    intro q hq
    exact pivotInversionCircleWitness_mem cfg p c q hq
  have haway : p ∉ geometricBlockSupport cfg b := by
    simpa [pivotInversionCircleBackBlock, b, A] using
      pivotInversionCircleBackBlock_away cfg p c
  have hinvEq : invertedAwayGeometricBlockCircle cfg p b haway =
      properCircumcircle (pivotInversion cfg p) t := by
    apply properCircle_eq_properCircumcircle_of_support
      (pivotInversion cfg p) t
    intro q hq
    have hqA : q.1 ∈ A.1 := by
      simpa [A, t] using
        pivotInversionCircleWitness_mem_backTriple cfg p c q hq
    have hqB : q.1 ∈ geometricBlockSupport cfg b := by
      simpa [b] using (geometricTripleOwner_contains cfg A hqA)
    have hinv := inversion_mem_invertedAwayGeometricBlockCircle
      cfg p b haway q.1 hqB
    simpa [pivotInversion] using hinv
  simpa [pivotInversionCircleBackBlock, b, A] using hcEq.trans hinvEq.symm

/-- The actual codomain used for the reverse circle dictionary: nontrivial
geometric blocks that avoid the inversion pivot. -/
abbrev PivotInversionAwayBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) :=
  {b : GeometricBlock cfg //
    3 ≤ (geometricBlockSupport cfg b).card ∧
      p ∉ geometricBlockSupport cfg b}

/-- Send each determined inverted circle to its unique away original owner. -/
noncomputable def pivotInversionCircleToAwayBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) :
    DeterminedCircle (pivotInversion cfg p) →
      PivotInversionAwayBlock cfg p := fun c =>
  ⟨pivotInversionCircleBackBlock cfg p c,
    three_le_pivotInversionCircleBackBlock_support cfg p c,
    pivotInversionCircleBackBlock_away cfg p c⟩

/-- The reverse dictionary is injective because inversion of its image is
exactly the circle from which the witness triple was chosen. -/
theorem pivotInversionCircleToAwayBlock_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) :
    Function.Injective (pivotInversionCircleToAwayBlock cfg p) := by
  intro c d hcd
  apply Subtype.ext
  let inv : PivotInversionAwayBlock cfg p → ProperCircle := fun b =>
    invertedAwayGeometricBlockCircle cfg p b.1 b.2.2
  have hinv : inv (pivotInversionCircleToAwayBlock cfg p c) =
      inv (pivotInversionCircleToAwayBlock cfg p d) :=
    congrArg inv hcd
  calc
    c.1 = inv (pivotInversionCircleToAwayBlock cfg p c) := by
      simpa [inv, pivotInversionCircleToAwayBlock] using
        pivotInversionCircleBackBlock_inverted_eq cfg p c
    _ = inv (pivotInversionCircleToAwayBlock cfg p d) := hinv
    _ = d.1 := by
      simpa [inv, pivotInversionCircleToAwayBlock] using
        (pivotInversionCircleBackBlock_inverted_eq cfg p d).symm

end Erdos506.V1
