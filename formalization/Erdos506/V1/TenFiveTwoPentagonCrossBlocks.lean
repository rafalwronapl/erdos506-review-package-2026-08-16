import Erdos506.V1.TenFiveTwoPentagonSaturation

/-!
# Selecting saturated two-pentagon cross-blocks

The five-by-five saturation equivalence turns every compatible pair of
exclusive chords into a unique cross-block.  This small V1 wrapper keeps all
dependent circle parameters inside `TenTwoPentagonSaturationData` and exposes
the exact chord projections needed by the golden-axis construction.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

noncomputable abbrev CompatibleChordPair
    (d : TenTwoPentagonSaturationData cfg) :=
  ↑(compatiblePairs
    (firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne)
    (secondExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne))

/-- The unique saturated cross-block representing a compatible chord pair. -/
noncomputable def crossBlockOfCompatiblePair
    (d : TenTwoPentagonSaturationData cfg)
    (p : d.CompatibleChordPair) :
    CircleCrossBlock cfg d.base.Γ d.base.Ω :=
  d.fiveFive.crossBlockEquiv.symm p

/-- Bundle an explicit pair of chords whose radical-axis centres agree. -/
noncomputable def compatibleChordPairOfEq
    (d : TenTwoPentagonSaturationData cfg)
    (e : CircleChord (exclusiveCircleTrace cfg d.base.Γ d.base.Ω))
    (k : CircleChord (exclusiveCircleTrace cfg d.base.Ω d.base.Γ))
    (hcenter :
      firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne e =
        secondExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne k) :
    d.CompatibleChordPair :=
  ⟨(e, k), (mem_compatiblePairs _ _ _ _).2 hcenter⟩

@[simp] theorem compatibleChordPairOfEq_fst
    (d : TenTwoPentagonSaturationData cfg)
    (e : CircleChord (exclusiveCircleTrace cfg d.base.Γ d.base.Ω))
    (k : CircleChord (exclusiveCircleTrace cfg d.base.Ω d.base.Γ))
    (hcenter) :
    (d.compatibleChordPairOfEq e k hcenter).1.1 = e := rfl

@[simp] theorem compatibleChordPairOfEq_snd
    (d : TenTwoPentagonSaturationData cfg)
    (e : CircleChord (exclusiveCircleTrace cfg d.base.Γ d.base.Ω))
    (k : CircleChord (exclusiveCircleTrace cfg d.base.Ω d.base.Γ))
    (hcenter) :
    (d.compatibleChordPairOfEq e k hcenter).1.2 = k := rfl

@[simp] theorem crossBlockChordPair_crossBlockOfCompatiblePair
    (d : TenTwoPentagonSaturationData cfg)
    (p : d.CompatibleChordPair) :
    crossBlockChordPair cfg d.base.Γ d.base.Ω
      (d.crossBlockOfCompatiblePair p) = p.1 := by
  exact d.fiveFive.crossBlockEquiv_symm_val p

@[simp] theorem crossBlockFirstChord_crossBlockOfCompatiblePair
    (d : TenTwoPentagonSaturationData cfg)
    (p : d.CompatibleChordPair) :
    crossBlockFirstChord cfg d.base.Γ d.base.Ω
        (d.crossBlockOfCompatiblePair p) = p.1.1 := by
  have h := d.crossBlockChordPair_crossBlockOfCompatiblePair p
  exact congrArg Prod.fst h

@[simp] theorem crossBlockSecondChord_crossBlockOfCompatiblePair
    (d : TenTwoPentagonSaturationData cfg)
    (p : d.CompatibleChordPair) :
    crossBlockSecondChord cfg d.base.Γ d.base.Ω
        (d.crossBlockOfCompatiblePair p) = p.1.2 := by
  have h := d.crossBlockChordPair_crossBlockOfCompatiblePair p
  exact congrArg Prod.snd h

@[simp] theorem crossBlockOfCompatiblePair_kind_circle
    (d : TenTwoPentagonSaturationData cfg)
    (p : d.CompatibleChordPair) :
    geometricBlockKind (d.crossBlockOfCompatiblePair p).1 = .circle :=
  d.crossBlock_kind_circle (d.crossBlockOfCompatiblePair p)

end TenTwoPentagonSaturationData

end Erdos506.V1
