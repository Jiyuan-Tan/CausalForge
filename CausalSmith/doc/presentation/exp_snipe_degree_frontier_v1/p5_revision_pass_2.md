# Holistic revision pass 2

- mode: local
- source digest before: `f694e87d3d1f5f8bc82041afe79266496e8ed3a6ab265ec1c2aea6d2117651d6`
- source digest after: `a3ac93bcb8b4b312b2903115f613cb0282b2e7d6cbdc9eb2d27319e94af84324`

## Reviser report

Implemented the P5 holistic revision pass in the presentation bundle.

Changed:
- [front_matter.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/front_matter.tex)
- [outline.md](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/outline.md)
- [sections/01_setup_and_assumptions.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/01_setup_and_assumptions.tex)
- [sections/02_main_results.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/02_main_results.tex)
- [sections/03_discussion_and_extensions.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/sections/03_discussion_and_extensions.tex)
- [appendix_proofs.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/appendix_proofs.tex)
- [proofs/thm:fair-coin-energy-frontier.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/proofs/thm:fair-coin-energy-frontier.tex)
- [paper.tex](/<repo-root>/CausalSmith/doc/presentation/exp_snipe_degree_frontier_v1/paper.tex)

Addressed:
- Corrected the coefficient-class projection prose to say clipped SNIPE projects to `[-B,B]` for the coefficient-mass risk comparison.
- Replaced the dense notation paragraph with a compact role/use table.
- Expanded the Cortez-Rodriguez, Eichhorn, and Yu comparison with a clearer split between their SNIPE/variance analysis and this paper’s minimax, lower-bound, bounded-outcome, and local-linear contributions.
- Removed math-mode `\cref` wrappers in proof prose that was not frozen formal text.
- Reframed explanatory “degree-one” prose as “first-order interactions `(\beta=1)`” where editable.

Verification:
- Ran `latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex`; build succeeds.
- Grep checks found no remaining `sharpens`, no old “target range” phrase, and no contribution-by-negation prose hits.

Residual:
- The remaining “Degree-one” / “degree-one” and `\(\cref{...}\)` occurrences are inside frozen formal theorem/definition bodies. I left those byte-faithful to the verified formal layer, per the hard boundary.
