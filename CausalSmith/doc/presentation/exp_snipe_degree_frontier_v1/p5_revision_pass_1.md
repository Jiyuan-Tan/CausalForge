# Holistic revision pass 1

- mode: local
- source digest before: `96401ec781a331a6982d6ba4ee46bc9411347f0b1b13f0b795e4a3973cb7555b`
- source digest after: `825ac1f36f5391973b14e90ced190024e9dad906d83168bb3a9fd43459964909`

## Reviser report

Implemented the holistic revision pass and mirrored the revised prose into [paper.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/paper.tex:1).

Changed:
- [front_matter.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/front_matter.tex:6): clarified fair-coin first-order scope as `\beta=1`, fixed the representer attribution/scope, and reframed the bounded-outcome summary.
- [sections/01_setup_and_assumptions.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/01_setup_and_assumptions.tex:7): added a compact notation map grouping global risk, block Riesz, least-favourable prior, and local-linear objects.
- [sections/02_main_results.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/02_main_results.tex:299): added the bounded-outcome lower-bound source via carrierwise containment.
- Proof prose files: cleaned non-frozen math-wrapped `\cref` occurrences.
- [outline.md](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/outline.md:80): updated the setup plan to reflect the notation map.
- [paper.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/paper.tex:11): removed the machine-generated author footnote language.

Verification:
- Ran `latexmk -pdf -interaction=nonstopmode paper.tex` successfully.
- Scans confirm the targeted prose defects are gone from authored prose and `paper.tex`.

Residual:
- Math-wrapped `\cref` remains inside frozen formal statement bodies copied from the verified formal layer. I left those byte-faithful because the prompt forbids changing frozen formal-layer content; fixing those requires upstream formal-layer regeneration.
