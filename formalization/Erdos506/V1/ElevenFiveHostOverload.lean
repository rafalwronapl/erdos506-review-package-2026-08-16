import Erdos506.V1.ElevenFive

/-!
# The eleven-five host-overload face

The `C = 39`, `L = 12` remaining geometric field is phrased as a positive
host-overload witness.  This module records that such a witness is already
incompatible with the finite two-host capacity, independently of any
real-plane principle.  Thus the outstanding work for that field is solely
to derive its displayed witness from the `C = 39` face.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem

universe u v

/-- On eleven points, a five-set cannot have outsider-pair host weight at
least thirty-one.  This is the exact contradiction consumed by the
`c39MaximumHostOverload` face. -/
theorem elevenFive_hostOverload_absurd
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hover : 31 <= elevenFiveHostWeight S D) : False := by
  have hcap := elevenFiveHostWeight_le_thirty S D hpoint hD
  omega

end Erdos506.V1
