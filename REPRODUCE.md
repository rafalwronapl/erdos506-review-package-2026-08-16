# Reproduction Guide

Run these commands from the artifact root. A first Lean build creates a local
`.lake` directory and may need network access to obtain the pinned mathlib
revision. Do not include that generated directory in a redistributed archive.

## Lean

```powershell
Set-Location formalization
lake -Kjobs=1 build Erdos506.V1.Main
lake -Kjobs=1 build Erdos506
lake env lean -DwarningAsError=true AxiomsAudit.lean
```

The toolchain is Lean 4.30.0 and the manifest pins mathlib to the v4.30.0
revision. The expected results are 8885 jobs, 8888 jobs, and `PASS` for the
strict audit, respectively. Normal builds may print non-fatal linter warnings.

## Source hygiene

From the artifact root:

```powershell
rg -n --glob '*.lean' '\bsorry\b|\badmit\b' formalization\Erdos506 formalization\Erdos506.lean
rg -n --glob '*.lean' '^\s*(axiom|unsafe)\b' formalization\Erdos506 formalization\Erdos506.lean
```

The first two commands should return no source declarations. The source also
contains three retained `native_decide` checks in
`formalization/Erdos506/Finite/UngarSixEvenAllowable.lean`; that module is not
imported by the current public root and none of its declarations occurs in the
public axiom audit. Textual matches in comments or identifiers should be
reviewed rather than treated as proof failures.

## Checksums

To verify the payload manifest in PowerShell:

```powershell
Get-Content CHECKSUMS.sha256 | ForEach-Object {
  $expected, $relative = $_ -split '  ', 2
  if ((Get-FileHash -Algorithm SHA256 -LiteralPath $relative).Hash.ToLower() -ne $expected) {
    throw "checksum mismatch: $relative"
  }
}
```

## Manuscript

```powershell
Set-Location paper
python verify_manuscript.py
python verify_simplifications.py
python supplement\verify_n13_gamma5_global_closure.py
```

The expected outputs are recorded in `audit/RESULTS.md`. The PDF is included
for convenience; the source and verification scripts are the review payload.

## Corrected n=6 replay

```powershell
Set-Location audit\n6_corrected
python -m pip install -r requirements.txt
python erdos506_n6_survivor_geometry.py
```

This replay checks the rational eight-circle witness and the similarity-safe
small-case identities. Its own README states its scope and limitations.
