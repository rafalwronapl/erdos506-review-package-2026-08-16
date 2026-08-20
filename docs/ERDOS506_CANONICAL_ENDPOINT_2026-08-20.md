# Exact canonical endpoint audit (2026-08-20)

The source now exports `Erdos506.erdos_506`, an exact `IsLeast` result over
the same mathematical predicate used by
`FormalConjectures/ErdosProblems/506.lean`:

- a finite set of points in the real Euclidean plane;
- cardinality `n`;
- not collinear;
- not cospherical;
- the set-based number of spheres through at least three selected points.

The answer is `Erdos506.v1Target n`: `3,5,8,11,17` for `n=4,...,8`, and
`1 + choose (n-1) 2 - (n-1)/2` from `n=9` onward.

## Bridge and sharpness

`Erdos506.numCircles_pointSet_eq_circleCount` proves that the official
set-based sphere count equals the internal determined-proper-circle count.
The proof constructs an equivalence between spheres containing at least three
selected points and internal determined circles, including a proof that every
such sphere has positive radius.

`Erdos506.V1.exists_v1_extremizer` supplies sharp constructions for every
`n >= 4`. The exceptional cases `n=6,7,8` have explicit coordinate
certificates; all other cases use the paired circle-and-centre family.

## Verification

```text
Erdos506.V1.Sharpness: PASS, 8892 jobs
Erdos506.Canonical: PASS, 8893 jobs
Erdos506 public root: PASS, 8896 jobs
AxiomsAudit.lean: PASS
```

The final endpoint's axiom report is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` or project-local axiom in the audited endpoint.
