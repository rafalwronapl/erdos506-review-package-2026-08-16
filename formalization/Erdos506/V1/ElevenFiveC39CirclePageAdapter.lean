import Erdos506.V1.ElevenFiveC39HostSaturation
import Erdos506.Incidence.FiveConicCirclePageBridge

/-!
# Labelled adapter for the circle-page K2.1 endpoint

The incidence theorem in `FiveConicCirclePageBridge` is stated on actual
points of the real plane.  This file is its lossless configuration adapter:
all inputs are memberships of labelled `DeterminedCircle` traces and all
inequalities are inequalities of labels or determined circles.

It intentionally does not claim that a host is a circle when it might be a
line.  That remaining generalized-carrier conversion is the exact boundary
between this actual K2.1 endpoint and the H=30/H=29 router.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The labelled, actual configuration form of the all-double triangle
obstruction for a proper-circle page.  The four labels `a,b,c,d` are the
marked complement of the page label; the six displayed hosts are the two
actual circle hosts for each outsider edge. -/
theorem elevenFive_circlePage_allDoubleTriangle_absurd
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
    (CAB CCD CAC CBD CAD CBC : DeterminedCircle cfg)
    (hCABCCD : CAB ≠ CCD) (hCACCBD : CAC ≠ CBD)
    (hCADCBC : CAD ≠ CBC)
    (haCAB : a ∈ circleTrace cfg CAB.1)
    (hbCAB : b ∈ circleTrace cfg CAB.1)
    (hxCAB : x ∈ circleTrace cfg CAB.1)
    (hyCAB : y ∈ circleTrace cfg CAB.1)
    (hcCCD : c ∈ circleTrace cfg CCD.1)
    (hdCCD : d ∈ circleTrace cfg CCD.1)
    (hxCCD : x ∈ circleTrace cfg CCD.1)
    (hyCCD : y ∈ circleTrace cfg CCD.1)
    (haCAC : a ∈ circleTrace cfg CAC.1)
    (hcCAC : c ∈ circleTrace cfg CAC.1)
    (hxCAC : x ∈ circleTrace cfg CAC.1)
    (hzCAC : z ∈ circleTrace cfg CAC.1)
    (hbCBD : b ∈ circleTrace cfg CBD.1)
    (hdCBD : d ∈ circleTrace cfg CBD.1)
    (hxCBD : x ∈ circleTrace cfg CBD.1)
    (hzCBD : z ∈ circleTrace cfg CBD.1)
    (haCAD : a ∈ circleTrace cfg CAD.1)
    (hdCAD : d ∈ circleTrace cfg CAD.1)
    (hyCAD : y ∈ circleTrace cfg CAD.1)
    (hzCAD : z ∈ circleTrace cfg CAD.1)
    (hbCBC : b ∈ circleTrace cfg CBC.1)
    (hcCBC : c ∈ circleTrace cfg CBC.1)
    (hyCBC : y ∈ circleTrace cfg CBC.1)
    (hzCBC : z ∈ circleTrace cfg CBC.1) : False := by
  apply properCircle_circlePage_allDoubleTriangle_absurd Gamma.1 K.1
    (CAB := CAB.1) (CCD := CCD.1) (CAC := CAC.1) (CBD := CBD.1)
    (CAD := CAD.1) (CBC := CBC.1)
  · exact mem_circleTrace.mp haGamma
  · exact mem_circleTrace.mp hbGamma
  · exact mem_circleTrace.mp hcGamma
  · exact mem_circleTrace.mp hdGamma
  · exact cfg.injective.ne hab
  · exact cfg.injective.ne hac
  · exact cfg.injective.ne had
  · exact cfg.injective.ne hbc
  · exact cfg.injective.ne hbd
  · exact cfg.injective.ne hcd
  · exact mem_circleTrace.mp hxK
  · exact mem_circleTrace.mp hyK
  · exact mem_circleTrace.mp hzK
  · exact cfg.injective.ne hxy
  · exact cfg.injective.ne hxz
  · exact cfg.injective.ne hyz
  · intro haK
    exact haNotK (mem_circleTrace.mpr haK)
  · intro hbK
    exact hbNotK (mem_circleTrace.mpr hbK)
  · intro hcK
    exact hcNotK (mem_circleTrace.mpr hcK)
  · intro hdK
    exact hdNotK (mem_circleTrace.mpr hdK)
  · intro hxGamma
    exact hxNotGamma (mem_circleTrace.mpr hxGamma)
  · intro hyGamma
    exact hyNotGamma (mem_circleTrace.mpr hyGamma)
  · intro hzGamma
    exact hzNotGamma (mem_circleTrace.mpr hzGamma)
  · exact determinedCircle_coe_ne_of_ne hCABCCD
  · exact determinedCircle_coe_ne_of_ne hCACCBD
  · exact determinedCircle_coe_ne_of_ne hCADCBC
  · exact mem_circleTrace.mp haCAB
  · exact mem_circleTrace.mp hbCAB
  · exact mem_circleTrace.mp hxCAB
  · exact mem_circleTrace.mp hyCAB
  · exact mem_circleTrace.mp hcCCD
  · exact mem_circleTrace.mp hdCCD
  · exact mem_circleTrace.mp hxCCD
  · exact mem_circleTrace.mp hyCCD
  · exact mem_circleTrace.mp haCAC
  · exact mem_circleTrace.mp hcCAC
  · exact mem_circleTrace.mp hxCAC
  · exact mem_circleTrace.mp hzCAC
  · exact mem_circleTrace.mp hbCBD
  · exact mem_circleTrace.mp hdCBD
  · exact mem_circleTrace.mp hxCBD
  · exact mem_circleTrace.mp hzCBD
  · exact mem_circleTrace.mp haCAD
  · exact mem_circleTrace.mp hdCAD
  · exact mem_circleTrace.mp hyCAD
  · exact mem_circleTrace.mp hzCAD
  · exact mem_circleTrace.mp hbCBC
  · exact mem_circleTrace.mp hcCBC
  · exact mem_circleTrace.mp hyCBC
  · exact mem_circleTrace.mp hzCBC

end Erdos506.V1
