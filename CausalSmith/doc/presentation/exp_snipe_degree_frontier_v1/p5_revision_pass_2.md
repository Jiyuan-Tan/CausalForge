# Holistic revision pass 2

- mode: reframe
- source digest before: `7ade99c7eff41a289d18b2f8ed8f47a88106266cea5723a2da0006ff68375fb3`
- source digest after: `a874e414bccf670bac444eb82e15421341990adab124d5f4cdeec2978feefdcd`

## Reviser report

Revised the authored sources for pass 2.

Changed:
- `front_matter.tex`
- `sections/02_setup_and_assumptions.tex`
- `sections/03_main_results.tex`
- `sections/04_discussion_and_extensions.tex`
- `sections/06_appendix_verification_note.tex`
- mirrored the relevant prose fixes into older same-role section variants: `sections/01_setup_and_assumptions.tex`, `sections/02_main_results.tex`, `sections/03_discussion_and_extensions.tex`, `sections/05_appendix_verification_note.tex`

Addressed:
- fixed-parameter abstract scope and SNIPE first-use gloss
- score-indexing clarification after `\cref{obj:def:snipe-score}`
- main-results roadmap and more interpretive theorem map
- complete-block wording so it calibrates degree dependence and exact unprojected-SNIPE risk without implying global all-estimator constants
- fixed-\((\beta,p)\) saturation qualification
- verification-note wording for checked unbiasedness/risk/exact-block statements
- added a short intuitive intro paragraph for reader accessibility

Declined/escalated:
- `stale-formal-dependency-footnote`: the stale author footnote exists only in derived `paper.tex`; the editable `front_matter.tex` has no `\author`/`\thanks` source. Editing `paper.tex` would violate the prompt and be discarded on reassembly. This needs the upstream title-page/template/meta source changed.

Verification:
- Ran targeted source searches for forbidden legacy cross-reference forms and stale routed phrases.
- Ran `git diff --check` on the active edited source set successfully.
- Did not rebuild `paper.tex`/PDF because that requires the P2 reassembler to rewrite protected derived artifacts.
