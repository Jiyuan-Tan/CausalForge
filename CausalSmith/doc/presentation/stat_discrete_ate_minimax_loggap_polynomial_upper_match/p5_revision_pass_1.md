# Holistic revision pass 1

- mode: local
- source digest before: `afc80ffd6d1543aad01aaabfc487ffb5cfb6e9fa9237cefddde3137f0c774160`
- source digest after: `ad1a924f763b5c96c2b640d8b0042ac0e73250e381d2c44c7ab039aa3751a777`

## Reviser report

Revised the manuscript in the authored sources and mirrored the changes into `paper.tex`.

Source files changed:
- `front_matter.tex`
- `outline.md`
- `sections/01_setup_and_assumptions.tex`
- `sections/02_main_results.tex`
- `sections/03_discussion_and_extensions.tex`
- `sections/05_appendix_verification_note.tex`
- `paper.tex`

Findings addressed:
- Tightened every prose summary of the near-randomization selected envelope to state the fixed-interior scope: fixed `0<epsilon<1/2`, `n>=N_epsilon`, and `d<=rho_epsilon n log n`.
- Removed the duplicate selected-estimator definition, keeping a single `synth_4` definition.
- Replaced “three equivalent readings” with “three consequences under the displayed fixed-interior range.”
- Revised the verification note to clarify that Lean checks the paper’s formal derivations subject to theorem-local external inputs.

Verification:
- Ran `latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex`.
- Build succeeded. The only remaining LaTeX warning is the existing `No \author given`.

No residual review finding requires work beyond rewriting.
