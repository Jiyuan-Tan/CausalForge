# Holistic revision pass 1

- mode: reframe
- source digest before: `535788aa8a15cc8526366da5db56404ada22952c97690d8ae8c426eb3cf87771`
- source digest after: `f1965dfbff7405ea03fb84ec0a27159cfbd5462c7b894059f6acdaacffb77022`

## Reviser report

Implemented the holistic revision pass and rebuilt the paper.

Changed:
- `sections/01_setup_transport_and_honest_risk.tex`
- `sections/02_oracle_frontier_and_score_inversion.tex`
- `sections/03_fixed_geometry_and_feasible_cell_weight_learning.tex`
- `sections/05_appendix_proofs_auxiliary_arguments_and_verification_note.tex`
- `proofs/thm:*.tex` proof narratives
- `appendix_proofs.tex`
- `outline.md`
- `paper.tex`
- `paper.pdf`

Addressed:
- Clarified finite-cell class as `\mathcal P_n` plus `\cref{obj:ass:finite-cell-source}`, with the repeated checklist framed as verification traceability.
- Reframed `\cref{obj:def:geometry-handle}` as the least-favorable separation calculation in surrounding prose while preserving the frozen formal body.
- Reordered appendix proofs into dependency order: fixed-geometry proof now precedes the no-shift proof.
- Rewrote implementation-style proof narration into standard asymptotic language.
- Clarified the oracle attainment carrier hypothesis as ambient carrier existence in reader-facing prose.
- Added the missing appendix label for `\cref{sec:deferred-proofs}`.

Verification:
- `latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex` passed and rebuilt `paper.pdf`.
- Formal environment bodies match `formal_layer.tex` by `obj_id`: 44/44, 0 mismatches.
- `appendix_proofs.tex` and `paper.tex` match the edited split proof sources.
- Scans passed for forbidden legacy refs and requested prose-pattern issues.
- `git diff --check` passed.

Residual: the `def:geometry-handle` anchor remains a frozen definition environment because changing its formal kind/body would violate the verification contract.
