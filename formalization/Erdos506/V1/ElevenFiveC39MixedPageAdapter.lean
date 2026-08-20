import Erdos506.V1.ElevenFiveC39HostFibreGeometry
import Erdos506.Incidence.FiveConicMixedPageBridge

/-!
# Actual mixed-host page adapter for the C39 K2.1 face

For a fixed outsider edge, a saturated C39 host fibre has two actual
generalized blocks.  They are either two circles or one circle and one line;
the line--line alternative is excluded by the unique affine line through the
outsider pair.  The mixed projective bridge proves the same trace-direction
conclusion in both remaining cases.

This file packages that literal case split at the labelled configuration
level.  Its public endpoint takes the three matched host pairs of an
all-double page and produces the K2.1 contradiction with no carrier-colour
assumption.  The only finite data displayed by the endpoint are the actual
memberships in the three pair fibres.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

private theorem elevenFive_pair_mem_outsidePairs
    (D : Finset α) {x y : α}
    (hx : x ∉ D) (hy : y ∉ D) (hxy : x ≠ y) :
    ({x, y} : Finset α) ∈ (Finset.univ \ D).powersetCard 2 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, by simp [hxy]⟩
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩

/-- A label absent from an actual determined line is absent from its
projective realization.  This is the line-page counterpart of the ordinary
circle-trace nonmembership used by the radical-axis bridge. -/
private theorem not_projectivePoint_orthogonal_determinedProjectiveLine_of_not_mem
    (cfg : Configuration α) (L : DeterminedLine cfg) (a : α)
    (ha : a ∉ lineSupport cfg L) :
    ¬ Projectivization.orthogonal (projectivePoint (cfg a))
      (determinedProjectiveLine cfg L) := by
  intro h
  apply ha
  apply mem_lineSupport.mpr
  apply (affinePoint_mem_determinedProjectiveLine_iff cfg a L).1
  simpa [affinePointToProjective_eq_projectivePoint] using h

/-- One actual double host fibre produces its selected-chord intersection on
the radical axis of a proper selected/page-circle pair, independently of
whether its second host is a line or a circle. -/
theorem elevenFive_mixedHostPair_direction_on_circlePage_axis
    (cfg : Configuration α) (Gamma K : DeterminedCircle cfg)
    (hGammaK : Gamma.1 ≠ K.1)
    {a b c d x y : α}
    (haGamma : a ∈ circleTrace cfg Gamma.1)
    (hbGamma : b ∈ circleTrace cfg Gamma.1)
    (hcGamma : c ∈ circleTrace cfg Gamma.1)
    (hdGamma : d ∈ circleTrace cfg Gamma.1)
    (haNotK : a ∉ circleTrace cfg K.1)
    (hcNotK : c ∉ circleTrace cfg K.1)
    (hxNotGamma : x ∉ circleTrace cfg Gamma.1)
    (hyNotGamma : y ∉ circleTrace cfg Gamma.1)
    (hxK : x ∈ circleTrace cfg K.1)
    (hyK : y ∈ circleTrace cfg K.1)
    (hab : a ≠ b) (hcd : c ≠ d) (hxy : x ≠ y)
    (B E : GeometricBlock cfg)
    (hB : B ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hE : E ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hBE : B ≠ E)
    (haB : a ∈ geometricBlockSupport cfg B)
    (hbB : b ∈ geometricBlockSupport cfg B)
    (hxB : x ∈ geometricBlockSupport cfg B)
    (hyB : y ∈ geometricBlockSupport cfg B)
    (hcE : c ∈ geometricBlockSupport cfg E)
    (hdE : d ∈ geometricBlockSupport cfg E)
    (hxE : x ∈ geometricBlockSupport cfg E)
    (hyE : y ∈ geometricBlockSupport cfg E) :
    Projectivization.orthogonal
      (Projectivization.cross
        (projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab))
        (projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd)))
      (projectiveRadicalAxis Gamma.1 K.1 hGammaK) := by
  classical
  have hA : ({x, y} : Finset α) ∈
      (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2 :=
    elevenFive_pair_mem_outsidePairs (circleTrace cfg Gamma.1)
      hxNotGamma hyNotGamma hxy
  rcases B with L | C
  · rcases E with M | F
    · exact False.elim
        (elevenFiveHostPairFibre_not_both_lines cfg
          (circleTrace cfg Gamma.1) {x, y} hA hB hE hBE
          ⟨L, M, rfl, rfl⟩)
    · have haL : a ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using haB
      have hbL : b ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using hbB
      have hxL : x ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using hxB
      have hyL : y ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using hyB
      have hcF : c ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hcE
      have hdF : d ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hdE
      have hxF : x ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hxE
      have hyF : y ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hyE
      have hGammaFdet : Gamma ≠ F := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxF
      have hGammaF : Gamma.1 ≠ F.1 :=
        determinedCircle_coe_ne_of_ne hGammaFdet
      have hFKdet : F ≠ K := by
        intro hEq
        apply hcNotK
        simpa [hEq] using hcF
      have hFK : F.1 ≠ K.1 := determinedCircle_coe_ne_of_ne hFKdet
      have hline :
          projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
            projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) :=
        projectiveLine_eq_projectiveLine_of_four_mem_determinedLine
          cfg L haL hbL hxL hyL hab hxy
      have h := properCircle_circleLineHost_direction_on_page_axis
        Gamma.1 K.1 F.1 hGammaK hGammaF hFK
        (a := cfg c) (b := cfg d) (c := cfg a) (d := cfg b)
        (x := cfg x) (y := cfg y)
        (mem_circleTrace.mp hcGamma) (mem_circleTrace.mp hdGamma)
        (mem_circleTrace.mp hcF) (mem_circleTrace.mp hdF)
        (mem_circleTrace.mp hxF) (mem_circleTrace.mp hyF)
        (mem_circleTrace.mp hxK) (mem_circleTrace.mp hyK)
        (by
          intro hcK
          exact hcNotK (mem_circleTrace.mpr hcK))
        (cfg.injective.ne hcd) (cfg.injective.ne hab)
        (cfg.injective.ne hxy) hline
      rw [Projectivization.cross_comm] at h
      exact h
  · rcases E with M | F
    · have haC : a ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using haB
      have hbC : b ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hbB
      have hxC : x ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hxB
      have hyC : y ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hyB
      have hcM : c ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hcE
      have hdM : d ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hdE
      have hxM : x ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hxE
      have hyM : y ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hyE
      have hGammaCdet : Gamma ≠ C := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxC
      have hGammaC : Gamma.1 ≠ C.1 :=
        determinedCircle_coe_ne_of_ne hGammaCdet
      have hCKdet : C ≠ K := by
        intro hEq
        apply haNotK
        simpa [hEq] using haC
      have hCK : C.1 ≠ K.1 := determinedCircle_coe_ne_of_ne hCKdet
      have hline :
          projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd) =
            projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) :=
        projectiveLine_eq_projectiveLine_of_four_mem_determinedLine
          cfg M hcM hdM hxM hyM hcd hxy
      exact properCircle_circleLineHost_direction_on_page_axis
        Gamma.1 K.1 C.1 hGammaK hGammaC hCK
        (mem_circleTrace.mp haGamma) (mem_circleTrace.mp hbGamma)
        (mem_circleTrace.mp haC) (mem_circleTrace.mp hbC)
        (mem_circleTrace.mp hxC) (mem_circleTrace.mp hyC)
        (mem_circleTrace.mp hxK) (mem_circleTrace.mp hyK)
        (by
          intro haK
          exact haNotK (mem_circleTrace.mpr haK))
        (cfg.injective.ne hab) (cfg.injective.ne hcd)
        (cfg.injective.ne hxy) hline
    · have haC : a ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using haB
      have hbC : b ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hbB
      have hxC : x ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hxB
      have hyC : y ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hyB
      have hcF : c ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hcE
      have hdF : d ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hdE
      have hxF : x ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hxE
      have hyF : y ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hyE
      have hGammaCdet : Gamma ≠ C := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxC
      have hGammaFdet : Gamma ≠ F := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxF
      have hGammaC : Gamma.1 ≠ C.1 :=
        determinedCircle_coe_ne_of_ne hGammaCdet
      have hGammaF : Gamma.1 ≠ F.1 :=
        determinedCircle_coe_ne_of_ne hGammaFdet
      have hCFdet : C ≠ F := by
        intro hEq
        apply hBE
        simpa [hEq]
      have hCF : C.1 ≠ F.1 := determinedCircle_coe_ne_of_ne hCFdet
      have hCKdet : C ≠ K := by
        intro hEq
        apply haNotK
        simpa [hEq] using haC
      have hCK : C.1 ≠ K.1 := determinedCircle_coe_ne_of_ne hCKdet
      exact properCircle_circleCircleHost_direction_on_page_axis
        Gamma.1 K.1 C.1 F.1 hGammaK hGammaC hGammaF hCF hCK
        (mem_circleTrace.mp haGamma) (mem_circleTrace.mp hbGamma)
        (mem_circleTrace.mp hcGamma) (mem_circleTrace.mp hdGamma)
        (mem_circleTrace.mp haC) (mem_circleTrace.mp hbC)
        (mem_circleTrace.mp hxC) (mem_circleTrace.mp hyC)
        (mem_circleTrace.mp hcF) (mem_circleTrace.mp hdF)
        (mem_circleTrace.mp hxF) (mem_circleTrace.mp hyF)
        (mem_circleTrace.mp hxK) (mem_circleTrace.mp hyK)
        (by
          intro haK
          exact haNotK (mem_circleTrace.mpr haK))
        (cfg.injective.ne hab) (cfg.injective.ne hcd)
        (cfg.injective.ne hxy)

/-- The literal mixed-carrier K2.1 endpoint for an actual proper-circle
page.  Each displayed pair of blocks is a saturated two-trace fibre over one
outsider edge.  The proof case-splits those actual carriers and reduces all
three edges to the common projective trace; hence no ``all hosts are
circles'' premise remains. -/
theorem elevenFive_mixedCirclePage_allDoubleTriangle_absurd
    (cfg : Configuration α) (Gamma K : DeterminedCircle cfg)
    {a b c d x y z : α}
    (haGamma : a ∈ circleTrace cfg Gamma.1)
    (hbGamma : b ∈ circleTrace cfg Gamma.1)
    (hcGamma : c ∈ circleTrace cfg Gamma.1)
    (hdGamma : d ∈ circleTrace cfg Gamma.1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxK : x ∈ circleTrace cfg K.1)
    (hyK : y ∈ circleTrace cfg K.1)
    (hzK : z ∈ circleTrace cfg K.1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (haNotK : a ∉ circleTrace cfg K.1)
    (hbNotK : b ∉ circleTrace cfg K.1)
    (hcNotK : c ∉ circleTrace cfg K.1)
    (hdNotK : d ∉ circleTrace cfg K.1)
    (hxNotGamma : x ∉ circleTrace cfg Gamma.1)
    (hyNotGamma : y ∉ circleTrace cfg Gamma.1)
    (hzNotGamma : z ∉ circleTrace cfg Gamma.1)
    (CAB CCD CAC CBD CAD CBC : GeometricBlock cfg)
    (hCABCCD : CAB ≠ CCD) (hCACCBD : CAC ≠ CBD)
    (hCADCBC : CAD ≠ CBC)
    (hCAB : CAB ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hCCD : CCD ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hCAC : CAC ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, z})
    (hCBD : CBD ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, z})
    (hCAD : CAD ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {y, z})
    (hCBC : CBC ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {y, z})
    (haCAB : a ∈ geometricBlockSupport cfg CAB)
    (hbCAB : b ∈ geometricBlockSupport cfg CAB)
    (hxCAB : x ∈ geometricBlockSupport cfg CAB)
    (hyCAB : y ∈ geometricBlockSupport cfg CAB)
    (hcCCD : c ∈ geometricBlockSupport cfg CCD)
    (hdCCD : d ∈ geometricBlockSupport cfg CCD)
    (hxCCD : x ∈ geometricBlockSupport cfg CCD)
    (hyCCD : y ∈ geometricBlockSupport cfg CCD)
    (haCAC : a ∈ geometricBlockSupport cfg CAC)
    (hcCAC : c ∈ geometricBlockSupport cfg CAC)
    (hxCAC : x ∈ geometricBlockSupport cfg CAC)
    (hzCAC : z ∈ geometricBlockSupport cfg CAC)
    (hbCBD : b ∈ geometricBlockSupport cfg CBD)
    (hdCBD : d ∈ geometricBlockSupport cfg CBD)
    (hxCBD : x ∈ geometricBlockSupport cfg CBD)
    (hzCBD : z ∈ geometricBlockSupport cfg CBD)
    (haCAD : a ∈ geometricBlockSupport cfg CAD)
    (hdCAD : d ∈ geometricBlockSupport cfg CAD)
    (hyCAD : y ∈ geometricBlockSupport cfg CAD)
    (hzCAD : z ∈ geometricBlockSupport cfg CAD)
    (hbCBC : b ∈ geometricBlockSupport cfg CBC)
    (hcCBC : c ∈ geometricBlockSupport cfg CBC)
    (hyCBC : y ∈ geometricBlockSupport cfg CBC)
    (hzCBC : z ∈ geometricBlockSupport cfg CBC) : False := by
  classical
  have hGammaKdet : Gamma ≠ K := by
    intro hEq
    apply hxNotGamma
    simpa [hEq] using hxK
  have hGammaK : Gamma.1 ≠ K.1 :=
    determinedCircle_coe_ne_of_ne hGammaKdet
  have hAB := elevenFive_mixedHostPair_direction_on_circlePage_axis
    cfg Gamma K hGammaK
    haGamma hbGamma hcGamma hdGamma haNotK hcNotK
    hxNotGamma hyNotGamma hxK hyK hab hcd hxy
    CAB CCD hCAB hCCD hCABCCD
    haCAB hbCAB hxCAB hyCAB hcCCD hdCCD hxCCD hyCCD
  have hAC := elevenFive_mixedHostPair_direction_on_circlePage_axis
    cfg Gamma K hGammaK
    haGamma hcGamma hbGamma hdGamma haNotK hbNotK
    hxNotGamma hzNotGamma hxK hzK hac hbd hxz
    CAC CBD hCAC hCBD hCACCBD
    haCAC hcCAC hxCAC hzCAC hbCBD hdCBD hxCBD hzCBD
  have hAD := elevenFive_mixedHostPair_direction_on_circlePage_axis
    cfg Gamma K hGammaK
    haGamma hdGamma hbGamma hcGamma haNotK hbNotK
    hyNotGamma hzNotGamma hyK hzK had hbc hyz
    CAD CBC hCAD hCBC hCADCBC
    haCAD hdCAD hyCAD hzCAD hbCBC hcCBC hyCBC hzCBC
  exact properCircle_allDoubleTriangle_projectiveLineTrace_absurd
    Gamma.1 (mem_circleTrace.mp haGamma) (mem_circleTrace.mp hbGamma)
    (mem_circleTrace.mp hcGamma) (mem_circleTrace.mp hdGamma)
    (cfg.injective.ne hab) (cfg.injective.ne hac) (cfg.injective.ne had)
    (cfg.injective.ne hbc) (cfg.injective.ne hbd) (cfg.injective.ne hcd)
    (projectiveRadicalAxis Gamma.1 K.1 hGammaK) hAB hAC hAD

/-! ## The same literal carrier split for a line page -/

theorem elevenFive_mixedHostPair_direction_on_linePage_axis
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg) (P : DeterminedLine cfg)
    {a b c d x y : α}
    (haGamma : a ∈ circleTrace cfg Gamma.1)
    (hbGamma : b ∈ circleTrace cfg Gamma.1)
    (hcGamma : c ∈ circleTrace cfg Gamma.1)
    (hdGamma : d ∈ circleTrace cfg Gamma.1)
    (haNotP : a ∉ lineSupport cfg P)
    (hcNotP : c ∉ lineSupport cfg P)
    (hxNotGamma : x ∉ circleTrace cfg Gamma.1)
    (hyNotGamma : y ∉ circleTrace cfg Gamma.1)
    (hxP : x ∈ lineSupport cfg P)
    (hyP : y ∈ lineSupport cfg P)
    (hab : a ≠ b) (hcd : c ≠ d) (hxy : x ≠ y)
    (B E : GeometricBlock cfg)
    (hB : B ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hE : E ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hBE : B ≠ E)
    (haB : a ∈ geometricBlockSupport cfg B)
    (hbB : b ∈ geometricBlockSupport cfg B)
    (hxB : x ∈ geometricBlockSupport cfg B)
    (hyB : y ∈ geometricBlockSupport cfg B)
    (hcE : c ∈ geometricBlockSupport cfg E)
    (hdE : d ∈ geometricBlockSupport cfg E)
    (hxE : x ∈ geometricBlockSupport cfg E)
    (hyE : y ∈ geometricBlockSupport cfg E) :
    Projectivization.orthogonal
      (Projectivization.cross
        (projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab))
        (projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd)))
      (determinedProjectiveLine cfg P) := by
  classical
  have hA : ({x, y} : Finset α) ∈
      (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2 :=
    elevenFive_pair_mem_outsidePairs (circleTrace cfg Gamma.1)
      hxNotGamma hyNotGamma hxy
  have hxyP : projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) =
      determinedProjectiveLine cfg P :=
    projectiveLine_eq_determinedProjectiveLine_of_mem cfg P hxP hyP hxy
  rcases B with L | C
  · rcases E with M | F
    · exact False.elim
        (elevenFiveHostPairFibre_not_both_lines cfg
          (circleTrace cfg Gamma.1) {x, y} hA hB hE hBE
          ⟨L, M, rfl, rfl⟩)
    · have haL : a ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using haB
      have hbL : b ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using hbB
      have hxL : x ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using hxB
      have hyL : y ∈ lineSupport cfg L := by
        simpa [geometricBlockSupport] using hyB
      have hcF : c ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hcE
      have hdF : d ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hdE
      have hxF : x ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hxE
      have hyF : y ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hyE
      have hGammaFdet : Gamma ≠ F := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxF
      have hGammaF : Gamma.1 ≠ F.1 :=
        determinedCircle_coe_ne_of_ne hGammaFdet
      have hABline :
          projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
            projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) :=
        projectiveLine_eq_projectiveLine_of_four_mem_determinedLine
          cfg L haL hbL hxL hyL hab hxy
      have h := properCircle_circleLineHost_direction_on_line_axis
        Gamma.1 F.1 hGammaF
        (a := cfg c) (b := cfg d) (c := cfg a) (d := cfg b)
        (determinedProjectiveLine cfg P)
        (mem_circleTrace.mp hcGamma) (mem_circleTrace.mp hdGamma)
        (mem_circleTrace.mp hcF) (mem_circleTrace.mp hdF)
        (not_projectivePoint_orthogonal_determinedProjectiveLine_of_not_mem
          cfg P c hcNotP)
        (cfg.injective.ne hcd) (cfg.injective.ne hab)
        (hABline.trans hxyP)
      rw [Projectivization.cross_comm] at h
      exact h
  · rcases E with M | F
    · have haC : a ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using haB
      have hbC : b ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hbB
      have hxC : x ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hxB
      have hyC : y ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hyB
      have hcM : c ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hcE
      have hdM : d ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hdE
      have hxM : x ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hxE
      have hyM : y ∈ lineSupport cfg M := by
        simpa [geometricBlockSupport] using hyE
      have hGammaCdet : Gamma ≠ C := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxC
      have hGammaC : Gamma.1 ≠ C.1 :=
        determinedCircle_coe_ne_of_ne hGammaCdet
      have hCDline :
          projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd) =
            projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) :=
        projectiveLine_eq_projectiveLine_of_four_mem_determinedLine
          cfg M hcM hdM hxM hyM hcd hxy
      exact properCircle_circleLineHost_direction_on_line_axis
        Gamma.1 C.1 hGammaC
        (determinedProjectiveLine cfg P)
        (mem_circleTrace.mp haGamma) (mem_circleTrace.mp hbGamma)
        (mem_circleTrace.mp haC) (mem_circleTrace.mp hbC)
        (not_projectivePoint_orthogonal_determinedProjectiveLine_of_not_mem
          cfg P a haNotP)
        (cfg.injective.ne hab) (cfg.injective.ne hcd)
        (hCDline.trans hxyP)
    · have haC : a ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using haB
      have hbC : b ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hbB
      have hxC : x ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hxB
      have hyC : y ∈ circleTrace cfg C.1 := by
        simpa [geometricBlockSupport] using hyB
      have hcF : c ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hcE
      have hdF : d ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hdE
      have hxF : x ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hxE
      have hyF : y ∈ circleTrace cfg F.1 := by
        simpa [geometricBlockSupport] using hyE
      have hGammaCdet : Gamma ≠ C := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxC
      have hGammaFdet : Gamma ≠ F := by
        intro hEq
        apply hxNotGamma
        simpa [hEq] using hxF
      have hGammaC : Gamma.1 ≠ C.1 :=
        determinedCircle_coe_ne_of_ne hGammaCdet
      have hGammaF : Gamma.1 ≠ F.1 :=
        determinedCircle_coe_ne_of_ne hGammaFdet
      have hCFdet : C ≠ F := by
        intro hEq
        apply hBE
        simpa [hEq]
      have hCF : C.1 ≠ F.1 := determinedCircle_coe_ne_of_ne hCFdet
      exact properCircle_circleCircleHost_direction_on_line_axis
        Gamma.1 C.1 F.1 hGammaC hGammaF hCF
        (determinedProjectiveLine cfg P)
        (mem_circleTrace.mp haGamma) (mem_circleTrace.mp hbGamma)
        (mem_circleTrace.mp hcGamma) (mem_circleTrace.mp hdGamma)
        (mem_circleTrace.mp haC) (mem_circleTrace.mp hbC)
        (mem_circleTrace.mp hxC) (mem_circleTrace.mp hyC)
        (mem_circleTrace.mp hcF) (mem_circleTrace.mp hdF)
        (mem_circleTrace.mp hxF) (mem_circleTrace.mp hyF)
        (not_projectivePoint_orthogonal_determinedProjectiveLine_of_not_mem
          cfg P a haNotP)
        (cfg.injective.ne hab) (cfg.injective.ne hcd)
        (cfg.injective.ne hxy) hxyP

/-- The literal mixed-carrier K2.1 endpoint for an actual determined-line
page.  It is parallel to the proper-circle-page endpoint above and covers
the other possible carrier of an `A13` or `A14` page. -/
theorem elevenFive_mixedLinePage_allDoubleTriangle_absurd
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg) (P : DeterminedLine cfg)
    {a b c d x y z : α}
    (haGamma : a ∈ circleTrace cfg Gamma.1)
    (hbGamma : b ∈ circleTrace cfg Gamma.1)
    (hcGamma : c ∈ circleTrace cfg Gamma.1)
    (hdGamma : d ∈ circleTrace cfg Gamma.1)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxP : x ∈ lineSupport cfg P)
    (hyP : y ∈ lineSupport cfg P)
    (hzP : z ∈ lineSupport cfg P)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (haNotP : a ∉ lineSupport cfg P)
    (hbNotP : b ∉ lineSupport cfg P)
    (hcNotP : c ∉ lineSupport cfg P)
    (hdNotP : d ∉ lineSupport cfg P)
    (hxNotGamma : x ∉ circleTrace cfg Gamma.1)
    (hyNotGamma : y ∉ circleTrace cfg Gamma.1)
    (hzNotGamma : z ∉ circleTrace cfg Gamma.1)
    (CAB CCD CAC CBD CAD CBC : GeometricBlock cfg)
    (hCABCCD : CAB ≠ CCD) (hCACCBD : CAC ≠ CBD)
    (hCADCBC : CAD ≠ CBC)
    (hCAB : CAB ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hCCD : CCD ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hCAC : CAC ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, z})
    (hCBD : CBD ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, z})
    (hCAD : CAD ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {y, z})
    (hCBC : CBC ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {y, z})
    (haCAB : a ∈ geometricBlockSupport cfg CAB)
    (hbCAB : b ∈ geometricBlockSupport cfg CAB)
    (hxCAB : x ∈ geometricBlockSupport cfg CAB)
    (hyCAB : y ∈ geometricBlockSupport cfg CAB)
    (hcCCD : c ∈ geometricBlockSupport cfg CCD)
    (hdCCD : d ∈ geometricBlockSupport cfg CCD)
    (hxCCD : x ∈ geometricBlockSupport cfg CCD)
    (hyCCD : y ∈ geometricBlockSupport cfg CCD)
    (haCAC : a ∈ geometricBlockSupport cfg CAC)
    (hcCAC : c ∈ geometricBlockSupport cfg CAC)
    (hxCAC : x ∈ geometricBlockSupport cfg CAC)
    (hzCAC : z ∈ geometricBlockSupport cfg CAC)
    (hbCBD : b ∈ geometricBlockSupport cfg CBD)
    (hdCBD : d ∈ geometricBlockSupport cfg CBD)
    (hxCBD : x ∈ geometricBlockSupport cfg CBD)
    (hzCBD : z ∈ geometricBlockSupport cfg CBD)
    (haCAD : a ∈ geometricBlockSupport cfg CAD)
    (hdCAD : d ∈ geometricBlockSupport cfg CAD)
    (hyCAD : y ∈ geometricBlockSupport cfg CAD)
    (hzCAD : z ∈ geometricBlockSupport cfg CAD)
    (hbCBC : b ∈ geometricBlockSupport cfg CBC)
    (hcCBC : c ∈ geometricBlockSupport cfg CBC)
    (hyCBC : y ∈ geometricBlockSupport cfg CBC)
    (hzCBC : z ∈ geometricBlockSupport cfg CBC) : False := by
  classical
  have hAB := elevenFive_mixedHostPair_direction_on_linePage_axis
    cfg Gamma P
    haGamma hbGamma hcGamma hdGamma haNotP hcNotP
    hxNotGamma hyNotGamma hxP hyP hab hcd hxy
    CAB CCD hCAB hCCD hCABCCD
    haCAB hbCAB hxCAB hyCAB hcCCD hdCCD hxCCD hyCCD
  have hAC := elevenFive_mixedHostPair_direction_on_linePage_axis
    cfg Gamma P
    haGamma hcGamma hbGamma hdGamma haNotP hbNotP
    hxNotGamma hzNotGamma hxP hzP hac hbd hxz
    CAC CBD hCAC hCBD hCACCBD
    haCAC hcCAC hxCAC hzCAC hbCBD hdCBD hxCBD hzCBD
  have hAD := elevenFive_mixedHostPair_direction_on_linePage_axis
    cfg Gamma P
    haGamma hdGamma hbGamma hcGamma haNotP hbNotP
    hyNotGamma hzNotGamma hyP hzP had hbc hyz
    CAD CBC hCAD hCBC hCADCBC
    haCAD hdCAD hyCAD hzCAD hbCBC hcCBC hyCBC hzCBC
  exact properCircle_allDoubleTriangle_projectiveLineTrace_absurd
    Gamma.1 (mem_circleTrace.mp haGamma) (mem_circleTrace.mp hbGamma)
    (mem_circleTrace.mp hcGamma) (mem_circleTrace.mp hdGamma)
    (cfg.injective.ne hab) (cfg.injective.ne hac) (cfg.injective.ne had)
    (cfg.injective.ne hbc) (cfg.injective.ne hbd) (cfg.injective.ne hcd)
    (determinedProjectiveLine cfg P) hAB hAC hAD

end Erdos506.V1
