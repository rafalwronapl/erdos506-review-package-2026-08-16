# Public Theorem Axiom Audit

The audit file is `formalization/AxiomsAudit.lean`. Run:

```powershell
Set-Location formalization
lake env lean -DwarningAsError=true AxiomsAudit.lean
```

The command passes. Every audited public declaration reports a subset of:

```text
[propext, Classical.choice, Quot.sound]
```

The current audit includes the V1 universal rows, large-range theorem, every
finite endpoint, the parameter-free V1 master, the parameter-free V3 lower
bound and extremal construction, and the complete V4 lower-bound/equality/
extremal surface.

This is a kernel-level dependency report for the listed declarations. It does
not replace mathematical review of the definitions, theorem statements, or
the modelling convention.

The wider source tree retains three `native_decide` checks in
`Finite/UngarSixEvenAllowable.lean`. That module is not imported by the current
public root and is not part of the declarations audited here.
