# Corrected `n=6` Replay

Run `python erdos506_n6_survivor_geometry.py` after installing
`sympy==1.14.0`.

The replay checks the exact rational witness with eight circles, enumerates
the small abstract Pasch pattern, and verifies the similarity-safe determinant
identities. It is a secondary arithmetic/control replay, not by itself a
standalone certificate of the complete lower-bound bridge.

The corresponding public Lean endpoint is
`../../formalization/Erdos506/V1/SmallSixClassifier.lean`, which supplies the
current kernel-checked n=6 lower-bound route.
