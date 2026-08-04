# Holistic revision pass 2

- mode: reframe
- source digest before: `874a9c46309097217c268db91ca255523c261feec89a2f41885284ad1265190d`
- source digest after: `61052eeae1c97a9d935b50e0bd10693155e4d06d74435b611003e22d27f34480`

## Reviser report

Implemented the P5 holistic reframe pass in the authored sources and mirrored it into `paper.tex`.

Changed:
- `front_matter.tex`, `outline.md`, `paper.tex`
- `sections/01_setup_transport_and_honest_risk.tex`
- `sections/02_oracle_frontier_and_score_inversion.tex`
- `sections/03_fixed_geometry_and_feasible_cell_weight_learning.tex`
- `sections/05_appendix_proofs_auxiliary_arguments_and_verification_note.tex`
- `appendix_proofs.tex`
- proof files for oracle score inversion, finite-cell attainment, fixed-geometry frontier, oracle converse, and regular-cell attainment

Addressed:
- Reframed the oracle score theorem’s admissible-geometry role as a carrier/nonempty-domain condition while keeping the law-by-law oracle score evaluation clear.
- Shortened receipt-transport explanation and moved target-sample procedure emphasis to the feasible section.
- Made the finite-cell submodel relation primary before the frozen checklist.
- Rewrote implementation-flavored proof phrases into conventional asymptotic/risk prose.
- Tightened the verification-note scope around checked theorem declarations and presentation-synthesized notation.
- Softened front-matter wording so the paper reads less formalization-forward.

Verification:
- `latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex` passed; `paper.pdf` rebuilt.
- Formal environment parity passed: `44` in `formal_layer.tex`, `44` in `paper.tex`, `0` mismatches.
- Proof files are exactly mirrored into both `appendix_proofs.tex` and `paper.tex`.
- No `\ref{}`, `\eqref{}`, or `\autoref{}` found in the editable manuscript sources.

Residual: the repeated finite-cell checklist remains inside the frozen verified definition body. Removing it from that environment would require an upstream formal-layer change; the surrounding prose now makes the one-line submodel relationship primary.
