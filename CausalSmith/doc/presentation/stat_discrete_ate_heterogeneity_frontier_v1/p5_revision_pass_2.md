# Holistic revision pass 2

- mode: reframe
- source digest before: `359537c04cc7e8d71d4e0586937add802e58bff45c596e52f2f6c1167309f79b`
- source digest after: `85a87155524a06c8d875c24e255da205ec649c001ca24d472d92fcbebc3663bc`

## Reviser report

Completed the holistic rewrite pass in the authored sources.

Changed:
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/front_matter.tex:1): reframed the abstract and introduction around a finite-sample minimax bracket, added first-use glosses for \(\epsilon\), \(M\), \(\sigma\), \(n\), and \(d\), and stated the exact-order matched regimes early.
- [sections/05_main_bracket_and_matched_regimes.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/05_main_bracket_and_matched_regimes.tex:200): added a schematic \((d,\sigma)\)-regime phase diagram and converted the regime summary into a labeled table.
- [sections/06_discussion_extensions_and_limitations.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/06_discussion_extensions_and_limitations.tex): tightened high-level phrasing from “main rates” to bracket-benchmark language.
- [sections/10_appendix_d_verification_note.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/10_appendix_d_verification_note.tex:3): updated the verification/trust-boundary prose to match the current contract, including the conditional status of the published binary collision comparison.

Findings addressed:
- Stale verification prose: addressed in Appendix D.
- Bracket versus full minimax characterization: addressed in abstract, introduction, main-regime prose, and discussion.
- Missing regime visualization: addressed with the new schematic figure.
- Benchmark notation repetition: reduced in revised prose; formal theorem restatements remain frozen.
- Overloaded exposition: improved with the roadmap, main theorem hierarchy language, and main-section visual/table organization. I did not move frozen formal environments beyond the existing outline constraints.

Residual / declined:
- The title itself and the author/title-block footnote appear outside the editable authored sources for this pass, with the visible stale footnote only in derived `paper.tex` or protected metadata. I left those untouched and tightened the editable verification note instead.
- The out-of-scope citation and implementation-appendix findings were not attempted.

Verification:
- Scanned authored sources for forbidden `\ref`, `\eqref`, and `\autoref`: clean.
- Scanned for the routed stale/trust-boundary phrases and prohibited contribution-by-negation patterns: clean.
- Ran a temporary LaTeX smoke compile over the authored sources: passed. I did not start a nested CausalSmith reassembly because the active parent `causalsmith present` process owns that step.
