# Holistic revision pass 1

- mode: local
- source digest before: `aa5e3618779c9e82f291002ec087620ccef271cffb9c778f6fff5a1198af7a80`
- source digest after: `663d086e9289dafb5df8e8649c136c5221dfbab6a82b7e94484953ccd9998e2d`

## Reviser report

Implemented the P5 revision pass in the authored sources.

Changed:
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/front_matter.tex)
- [sections/01_related_work.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/01_related_work.tex)
- [sections/02_setup_and_assumptions.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/02_setup_and_assumptions.tex)
- [sections/03_estimators_and_upper_bounds.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/03_estimators_and_upper_bounds.tex)
- [sections/05_main_bracket_and_matched_regimes.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/05_main_bracket_and_matched_regimes.tex)
- [sections/09_appendix_c_proofs_for_lower_bounds_and_regime_algebra.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/09_appendix_c_proofs_for_lower_bounds_and_regime_algebra.tex)
- [sections/10_appendix_d_verification_note.tex](<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_heterogeneity_frontier_v1/sections/10_appendix_d_verification_note.tex)

Addressed the routed rewrite findings: updated the verification commit, separated `\ell^{\mathrm{cap}}` from `\ell^{\mathrm{tri}}`, repaired the trust-boundary prose in authored text, narrowed the estimator calibration claim, renamed/scoped the residual-wedge table row, split the Zeng lower-bound comparison rows, clarified total computation as aggregation plus post-aggregation work, and introduced the benchmark-naming convention.

Verification performed:
- `lake -d ../../.. build` succeeded.
- `git diff --check` passed for changed files.
- Authored-source scans are clean for stale commit text, old overclaim/table wording, forbidden `\ref`/`\eqref`/`\autoref`, and the prohibited negative contribution-framing patterns.
- Paper-index check reported this bundle clean, though the repo-wide command still fails on unrelated bundles.

Residuals:
- The out-of-scope source-target notation finding for `thm:radius-channel-converse-all-d` was not attempted, per prompt.
- A generated author footnote/trust-boundary phrase remains in derived `paper.tex` via an upstream pipeline template outside the editable list. I did not edit the derived file or pipeline source. The official P2/P4 reassembly command is currently blocked by an existing active run lock at PID `1770863`.
