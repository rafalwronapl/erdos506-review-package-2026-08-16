import Erdos506.Incidence.SixConicActiveSignatureGeometry
import Mathlib.Tactic

/-!
# Three full six-conic signatures on one geometric host

The four real dihedral matchings are the only active full signatures.  The
common centre of every full edge carried by one generalized host lies on a
single projective line: the completion of a line host, or the radical axis
of a circle host with the selected six-point circle.  If four signatures
were present, the centres of `R3,S1` would identify that host line with the
shared chord `25`, while the centres of `R3,S3` would identify it with the
distinct chord `03`.  A proper circle has no three collinear points, giving
the required contradiction.

No event-principle field or additional geometric witness is used here.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

/-- Transport of the pencil action across equality of homogeneous centres.
The two nondegeneracy witnesses live in dependent types, but proof
irrelevance makes the resulting projective transformations identical after
the centres have been identified. -/
private theorem properCirclePencilGL_smul_eq_of_center_eq
    (c : ProperCircle) {o₀ o₁ : Homogeneous3}
    (ho : o₀ = o₁)
    (h₀ : properCirclePencilDeterminant c o₀ ≠ 0)
    (h₁ : properCirclePencilDeterminant c o₁ ≠ 0)
    (P : RealProjectiveOnePoint) :
    properCirclePencilGL c o₀ h₀ • P =
      properCirclePencilGL c o₁ h₁ • P := by
  subst o₁
  rfl

private theorem relabelR3_pair03
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 0, label 3} ∈
      relabelSixCycleMatching label (0 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{0, 3}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleR3Matching]
  · simp

private theorem relabelR3_pair14
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 1, label 4} ∈
      relabelSixCycleMatching label (0 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{1, 4}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleR3Matching]
  · simp

private theorem relabelR3_pair25
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 2, label 5} ∈
      relabelSixCycleMatching label (0 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{2, 5}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleR3Matching]
  · simp

private theorem relabelS1_pair01
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 0, label 1} ∈
      relabelSixCycleMatching label (1 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{0, 1}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleS1Matching]
  · simp

private theorem relabelS1_pair25
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 2, label 5} ∈
      relabelSixCycleMatching label (1 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{2, 5}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleS1Matching]
  · simp

private theorem relabelS3_pair03
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 0, label 3} ∈
      relabelSixCycleMatching label (2 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{0, 3}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleS3Matching]
  · simp

private theorem relabelS3_pair12
    {α : Type*} [DecidableEq α] (label : Fin 6 → α) :
    {label 1, label 2} ∈
      relabelSixCycleMatching label (2 : SixCycleInvolutionCode) := by
  rw [relabelSixCycleMatching]
  apply Finset.mem_image.mpr
  refine ⟨{1, 2}, ?_, ?_⟩
  · simp [sixCycleDihedralMatching, sixCycleS3Matching]
  · simp

/-- Centres belonging to full edges on one generalized host are incident
with a common projective line. -/
private theorem exists_sixConicHostCenterAxis
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) :
    ∃ axis : RealProjectivePlane,
      ∀ {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X),
        e ⊆ geometricBlockSupport cfg H →
          Projectivization.orthogonal
            (sixConicFullEdgeCenter
              cfg gamma hgamma X hdisjoint heFull) axis := by
  classical
  cases H with
  | inl L =>
      obtain ⟨D, hDL⟩ := L.exists_pair
      refine ⟨projectiveChordLine cfg D, ?_⟩
      intro e heFull heHost
      change e ⊆ lineSupport cfg L at heHost
      let pe : Erdos506.Finite.KSubset α 2 :=
        ⟨e, sixConicFullEdge_card
          cfg gamma hgamma X hdisjoint heFull⟩
      have heLine : lineOfPair cfg pe = L.1 :=
        lineOfPair_eq_of_mem_of_direction_finrank_one cfg pe L.1 (by
          intro x hx
          apply mem_lineSupport.mp
          exact heHost hx) L.direction_finrank
      have hprojective := projectiveChordLine_eq_of_lineOfPair_eq
        cfg pe D (heLine.trans hDL.symm)
      rw [← hprojective]
      exact sixConicFullEdgeCenter_on_outsiderChord
        cfg gamma hgamma X hdisjoint heFull
  | inr K =>
      by_cases hgammaK : gamma = K
      · let label := sixConicCyclicLabel cfg gamma hgamma
        refine ⟨projectivePoint (cfg (label 0).1), ?_⟩
        intro e heFull heHost
        change e ⊆ circleTrace cfg K.1 at heHost
        exfalso
        have heSpec := mem_sixConicFullEdges.mp heFull
        have hePow := Finset.mem_powersetCard.mp heSpec.1
        have heNonempty : e.Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨x, hxE⟩ := heNonempty
        have hxGamma : x ∈ circleTrace cfg gamma.1 := by
          have hxK : x ∈ circleTrace cfg K.1 := heHost hxE
          simpa only [hgammaK] using hxK
        have hxX : x ∈ X := hePow.1 hxE
        exact Finset.disjoint_left.mp hdisjoint hxGamma hxX
      · refine ⟨projectiveRadicalAxis gamma.1 K.1
          (determinedCircle_coe_ne_of_ne hgammaK), ?_⟩
        intro e heFull heHost
        change e ⊆ circleTrace cfg K.1 at heHost
        exact sixConicFullEdgeCenter_on_circleHostAxis
          cfg gamma hgamma X hdisjoint heFull K hgammaK heHost

/-- Field-free replacement for
the three-signature-on-one-host bound. -/
theorem sixConicSignaturesOnHost_card_le_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) :
    (sixConicSignaturesOnHost cfg gamma X H).card ≤ 3 := by
  classical
  let A := sixConicSignaturesOnHost cfg gamma X H
  have hAactive : A ⊆ sixConicActiveSignatures cfg gamma X := by
    intro signature hsignature
    dsimp only [A] at hsignature
    rw [sixConicSignaturesOnHost] at hsignature
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hsignature
    rw [sixConicActiveSignatures]
    exact Finset.mem_image.mpr
      ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
  have hAleFour : A.card ≤ 4 :=
    (Finset.card_le_card hAactive).trans
      (sixConic_activeSignatures_card_le_four
        cfg gamma hgamma X hdisjoint)
  by_contra hnot
  change ¬ A.card ≤ 3 at hnot
  have hAcard : A.card = 4 := by omega
  let witness := sixConic_activeSignature_dihedralWitness
    cfg gamma hgamma X hdisjoint
  let label := witness.cyclicLabel
  let ell : Fin 6 → α := fun i => (label i).1
  let candidates : Finset (Finset (Finset α)) :=
    (Finset.univ : Finset SixCycleInvolutionCode).image
      (relabelSixCycleMatching ell)
  have hAsubset : A ⊆ candidates := by
    intro signature hsignature
    obtain ⟨code, hcode⟩ :=
      witness.classified signature (hAactive hsignature)
    change signature = relabelSixCycleMatching ell code at hcode
    exact Finset.mem_image.mpr
      ⟨code, Finset.mem_univ code, hcode.symm⟩
  have hcandidatesLe : candidates.card ≤ 4 := by
    calc
      candidates.card ≤
          (Finset.univ : Finset SixCycleInvolutionCode).card := by
        dsimp only [candidates]
        exact Finset.card_image_le
      _ = 4 := by simp [SixCycleInvolutionCode]
  have hAcandidates : A = candidates := by
    apply Finset.eq_of_subset_of_card_le hAsubset
    have hle := Finset.card_le_card hAsubset
    omega
  have hcodeHost (code : SixCycleInvolutionCode) :
      relabelSixCycleMatching ell code ∈ A := by
    rw [hAcandidates]
    exact Finset.mem_image.mpr
      ⟨code, Finset.mem_univ code, rfl⟩
  have hedge (code : SixCycleInvolutionCode) :
      ∃ e : Finset α,
        e ∈ sixConicFullEdges cfg gamma X ∧
        e ⊆ geometricBlockSupport cfg H ∧
        sixConicSignature cfg gamma e =
          relabelSixCycleMatching ell code := by
    have hs := hcodeHost code
    dsimp only [A] at hs
    rw [sixConicSignaturesOnHost] at hs
    obtain ⟨e, he, hsignature⟩ := Finset.mem_image.mp hs
    exact ⟨e, (Finset.mem_filter.mp he).1,
      (Finset.mem_filter.mp he).2, hsignature⟩
  obtain ⟨e0, he0, he0Host, hsignature0⟩ :=
    hedge (0 : SixCycleInvolutionCode)
  obtain ⟨e1, he1, he1Host, hsignature1⟩ :=
    hedge (1 : SixCycleInvolutionCode)
  obtain ⟨e2, he2, he2Host, hsignature2⟩ :=
    hedge (2 : SixCycleInvolutionCode)
  let O0 := sixConicFullEdgeCenter
    cfg gamma hgamma X hdisjoint he0
  let O1 := sixConicFullEdgeCenter
    cfg gamma hgamma X hdisjoint he1
  let O2 := sixConicFullEdgeCenter
    cfg gamma hgamma X hdisjoint he2
  obtain ⟨axis, haxis⟩ :=
    exists_sixConicHostCenterAxis cfg gamma hgamma X hdisjoint H
  have haxis0 : Projectivization.orthogonal O0 axis := by
    exact haxis he0 he0Host
  have haxis1 : Projectivization.orthogonal O1 axis := by
    exact haxis he1 he1Host
  have haxis2 : Projectivization.orthogonal O2 axis := by
    exact haxis he2 he2Host
  have hellInjective : Function.Injective ell :=
    Subtype.val_injective.comp label.injective
  have h03 : label (0 : Fin 6) ≠ label 3 :=
    label.injective.ne (by decide)
  have h01 : label (0 : Fin 6) ≠ label 1 :=
    label.injective.ne (by decide)
  have h14 : label (1 : Fin 6) ≠ label 4 :=
    label.injective.ne (by decide)
  have h12 : label (1 : Fin 6) ≠ label 2 :=
    label.injective.ne (by decide)
  have h25 : label (2 : Fin 6) ≠ label 5 :=
    label.injective.ne (by decide)
  have h03e0 : {ell 0, ell 3} ∈ sixConicSignature cfg gamma e0 := by
    rw [hsignature0]
    exact relabelR3_pair03 ell
  have h14e0 : {ell 1, ell 4} ∈ sixConicSignature cfg gamma e0 := by
    rw [hsignature0]
    exact relabelR3_pair14 ell
  have h25e0 : {ell 2, ell 5} ∈ sixConicSignature cfg gamma e0 := by
    rw [hsignature0]
    exact relabelR3_pair25 ell
  have h01e1 : {ell 0, ell 1} ∈ sixConicSignature cfg gamma e1 := by
    rw [hsignature1]
    exact relabelS1_pair01 ell
  have h25e1 : {ell 2, ell 5} ∈ sixConicSignature cfg gamma e1 := by
    rw [hsignature1]
    exact relabelS1_pair25 ell
  have h03e2 : {ell 0, ell 3} ∈ sixConicSignature cfg gamma e2 := by
    rw [hsignature2]
    exact relabelS3_pair03 ell
  have h12e2 : {ell 1, ell 2} ∈ sixConicSignature cfg gamma e2 := by
    rw [hsignature2]
    exact relabelS3_pair12 ell
  have hO01 : O0 ≠ O1 := by
    intro hcenters
    have haction0 := sixConicFullEdgeCenter_pairs
      cfg gamma hgamma X hdisjoint he0 (label 0) (label 3) h03 h03e0
    have haction1 := sixConicFullEdgeCenter_pairs
      cfg gamma hgamma X hdisjoint he1 (label 0) (label 1) h01 h01e1
    have hparameters :
        sixConicTraceParameter cfg gamma (label 3) =
          sixConicTraceParameter cfg gamma (label 1) := by
      calc
        sixConicTraceParameter cfg gamma (label 3) =
            properCirclePencilGL gamma.1 O0.rep
              (sixConicFullEdgeCenter_nondegenerate
                cfg gamma hgamma X hdisjoint he0) •
              sixConicTraceParameter cfg gamma (label 0) := haction0
        _ = properCirclePencilGL gamma.1 O1.rep
              (sixConicFullEdgeCenter_nondegenerate
                cfg gamma hgamma X hdisjoint he1) •
              sixConicTraceParameter cfg gamma (label 0) := by
          apply properCirclePencilGL_smul_eq_of_center_eq
          exact congrArg Projectivization.rep hcenters
        _ = sixConicTraceParameter cfg gamma (label 1) := haction1.symm
    have hlabels :=
      sixConicTraceParameter_injective cfg gamma hparameters
    exact (by decide : (3 : Fin 6) ≠ 1) (label.injective hlabels)
  have hO02 : O0 ≠ O2 := by
    intro hcenters
    have haction0 := sixConicFullEdgeCenter_pairs
      cfg gamma hgamma X hdisjoint he0 (label 1) (label 4) h14 h14e0
    have haction2 := sixConicFullEdgeCenter_pairs
      cfg gamma hgamma X hdisjoint he2 (label 1) (label 2) h12 h12e2
    have hparameters :
        sixConicTraceParameter cfg gamma (label 4) =
          sixConicTraceParameter cfg gamma (label 2) := by
      calc
        sixConicTraceParameter cfg gamma (label 4) =
            properCirclePencilGL gamma.1 O0.rep
              (sixConicFullEdgeCenter_nondegenerate
                cfg gamma hgamma X hdisjoint he0) •
              sixConicTraceParameter cfg gamma (label 1) := haction0
        _ = properCirclePencilGL gamma.1 O2.rep
              (sixConicFullEdgeCenter_nondegenerate
                cfg gamma hgamma X hdisjoint he2) •
              sixConicTraceParameter cfg gamma (label 1) := by
          apply properCirclePencilGL_smul_eq_of_center_eq
          exact congrArg Projectivization.rep hcenters
        _ = sixConicTraceParameter cfg gamma (label 2) := haction2.symm
    have hlabels :=
      sixConicTraceParameter_injective cfg gamma hparameters
    exact (by decide : (4 : Fin 6) ≠ 2) (label.injective hlabels)
  let chord25 := projectiveLine (cfg (ell 2)) (cfg (ell 5))
    (cfg.injective.ne (hellInjective.ne (by decide)))
  let chord03 := projectiveLine (cfg (ell 0)) (cfg (ell 3))
    (cfg.injective.ne (hellInjective.ne (by decide)))
  have hO0Chord25 : Projectivization.orthogonal O0 chord25 := by
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint he0 (label 2) (label 5) h25 h25e0
  have hO1Chord25 : Projectivization.orthogonal O1 chord25 := by
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint he1 (label 2) (label 5) h25 h25e1
  have hO0Chord03 : Projectivization.orthogonal O0 chord03 := by
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint he0 (label 0) (label 3) h03 h03e0
  have hO2Chord03 : Projectivization.orthogonal O2 chord03 := by
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint he2 (label 0) (label 3) h03 h03e2
  have haxisEq25 : axis = chord25 := by
    calc
      axis = Projectivization.cross O0 O1 :=
        projectiveCovector_eq_cross_of_orthogonal
          hO01 haxis0 haxis1
      _ = chord25 :=
        (projectiveCovector_eq_cross_of_orthogonal
          hO01 hO0Chord25 hO1Chord25).symm
  have haxisEq03 : axis = chord03 := by
    calc
      axis = Projectivization.cross O0 O2 :=
        projectiveCovector_eq_cross_of_orthogonal
          hO02 haxis0 haxis2
      _ = chord03 :=
        (projectiveCovector_eq_cross_of_orthogonal
          hO02 hO0Chord03 hO2Chord03).symm
  have hchordsEq : chord25 = chord03 :=
    haxisEq25.symm.trans haxisEq03
  have hnotOn25 : ¬Projectivization.orthogonal
      (projectivePoint (cfg (ell 0))) chord25 := by
    exact properCircle_projectivePoint_not_on_chord gamma.1
      (mem_circleTrace.mp (label 2).2)
      (mem_circleTrace.mp (label 5).2)
      (mem_circleTrace.mp (label 0).2)
      (cfg.injective.ne (hellInjective.ne (by decide)))
      (cfg.injective.ne (hellInjective.ne (by decide)))
      (cfg.injective.ne (hellInjective.ne (by decide)))
  apply hnotOn25
  rw [hchordsEq]
  exact Projectivization.orthogonal_comm.mp
    (projectiveLine_orthogonal_left
      (cfg.injective.ne (hellInjective.ne (by decide))))

end Erdos506.Incidence
