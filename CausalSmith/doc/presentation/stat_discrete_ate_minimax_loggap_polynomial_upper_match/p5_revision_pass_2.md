# Holistic revision pass 2

- mode: reframe
- source digest before: `6b3f3e8a76cef77ffb5fff4f9eb9e8fa4626f5be38f0cb24c7f9e8db4c8fcf7d`
- source digest after: `412ee7f398373ff165911d71d3bc9d0e6774e1ffbef7baa0719c04eba22608c2`

## Reviser report

Implemented the revision pass in the presentation bundle.

Changed:
- [outline.md](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/outline.md)
- [front_matter.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/front_matter.tex)
- [paper.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/paper.tex)
- [sections/01_setup_and_assumptions.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/sections/01_setup_and_assumptions.tex)
- [sections/02_main_results.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/sections/02_main_results.tex)
- [sections/03_discussion_and_extensions.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/sections/03_discussion_and_extensions.tex)
- [sections/04_appendix_proofs_and_auxiliary_lemmas.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/sections/04_appendix_proofs_and_auxiliary_lemmas.tex)
- [sections/05_appendix_verification_note.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/sections/05_appendix_verification_note.tex)
- [appendix_proofs.tex](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/appendix_proofs.tex)
- proof snippets under [proofs/](/<repo-root>/CausalSmith/doc/presentation/stat_discrete_ate_minimax_loggap_polynomial_upper_match/proofs)

Addressed all P5 rewrite findings:
- Narrowed title and abstract to fixed-interior scope.
- Added explicit non-characterization outside `d <= rho_epsilon n log n` and for triangular arrays `epsilon_n -> 1/2`.
- Recast the selected estimator as an oracle-calibrated deterministic comparison, not a data-driven adaptive rule.
- Sharpened the Zeng et al. positioning: imported lower-bound ingredient versus new matching computable upper bound.
- Removed `% lean:` proof breadcrumbs and compressed convention-heavy proof prose; moved the verification-location explanation into the verification note.

Verification:
- Ran `latexmk -pdf -interaction=nonstopmode paper.tex` successfully.
- Remaining LaTeX messages are non-fatal layout/no-author warnings, not undefined references or citation failures.

No residual P5 rewrite finding remains. The adaptive selector and triangular-array transition remain explicit limitations rather than unresolved rewrite work.
