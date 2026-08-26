# Holistic revision pass 1

- mode: reframe
- source digest before: `77f71aa263f12cf1484776983e50cab4cc6e7a1c20c102f5a60fa384013fc4ab`
- source digest after: `b880fbcb352437ecc0ee006c7d747a7b7160f452628e60f48e72f76db030c689`

## Reviser report

Implemented the holistic rewrite pass in the authored sources.

Changed:
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/front_matter.tex): added first-use glosses for `\epsilon` and `M`, and reframed residual-wedge language as benchmark separation.
- [sections/01_related_work.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/01_related_work.tex): replaced the “inherited/new” paragraph with a clearer source-vs-current-contribution distinction.
- [sections/02_setup_and_assumptions.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/02_setup_and_assumptions.tex): added the requested benchmark notation table.
- [sections/03_estimators_and_upper_bounds.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/03_estimators_and_upper_bounds.tex): added an upper-bound proof roadmap and explained the polynomial estimator aggregation/operation-count claim.
- [sections/04_lower_bounds_and_binary_embeddings.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/04_lower_bounds_and_binary_embeddings.tex): added a lower-bound proof roadmap.
- [sections/05_main_bracket_and_matched_regimes.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/05_main_bracket_and_matched_regimes.tex): reframed the residual wedge row as localized displayed-benchmark separation.
- [sections/06_discussion_extensions_and_limitations.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/06_discussion_extensions_and_limitations.tex): renamed the printed section to `Discussion and limitations`.
- [sections/07_appendix_a_published_binary_ingredients.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/07_appendix_a_published_binary_ingredients.tex) and [sections/10_appendix_d_verification_note.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/10_appendix_d_verification_note.tex): updated verification-boundary prose to match the current contract.
- [proofs/lem:capped-exact-transport-package.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/proofs/lem:capped-exact-transport-package.tex) and [proofs/lem:zeng-usable-occupancy-reciprocal.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/proofs/lem:zeng-usable-occupancy-reciprocal.tex): translated implementation-ish proof wording into standard minimax/probability language.

Verification:
- Ran a local authored-source lint over 43 `.tex` files: clean for legacy refs, manual kind+`\cref`, and stale routed phrases.
- I did not run official `causalsmith present ... --from P2 --reassemble --stop-after P3` because a separate active presentation run is still live in this same bundle, with a live Codex child. Running a second reassembly would violate the project’s no-overlap guidance.

Residual:
- The stale author footnote exists only in derived `paper.tex`; per instructions I did not edit derived files. It needs regeneration or an upstream/source change outside the allowed authored-source list.
- The outside-scope binary class restatement finding was not attempted, as requested.
