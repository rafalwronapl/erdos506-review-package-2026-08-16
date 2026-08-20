# Erdős 506 V1 — review manuscript

This directory contains the publication-facing rewrite of the proof dossier.
It is deliberately separate from the operational ledger in `docs/` and from
the historical search material in `scratch/`.

The main source is `erdos506_v1_review_manuscript.tex`.  A review-ready version
must satisfy all of the following before circulation:

- no unresolved `% REVIEW GAP:` marker;
- every symbol is defined before use;
- every finite case is either proved in the text or reduced to a displayed
  coefficient table in an appendix;
- no local repository path, status label, agent name, or historical solver
  narrative appears in the mathematical exposition;
- the bibliography and all imported classical hypotheses are checked against
  the original sources;
- the source compiles without warnings that affect mathematical content.

The operational manifest and exact-arithmetic scripts remain the
reproducibility supplement; they are not part of the exposition submitted for
mathematical review.

The files SIMPLIFICATION_NOTES.md and verify_simplifications.py describe an
earlier deletion/\(n=16\) architecture and are retained only as historical
regressions.  The review manuscript must use the direct \(n=14\) dichotomy
and the uniform \(n\ge15\) functional from the frozen proof DAG.
