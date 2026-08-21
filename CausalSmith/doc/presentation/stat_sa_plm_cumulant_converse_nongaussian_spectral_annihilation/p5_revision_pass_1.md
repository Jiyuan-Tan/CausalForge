# Holistic revision pass 1

- mode: reframe
- source digest before: `33d99086ebe74ea777549a0aa867243d6790b88d37b71566b10cdb39903dfcfa`
- source digest after: `3cec4a1e174c4b17c277d8241a7f5923d1d1c681b3c3dfaf6eeb8ebb5a83577e`

## Reviser report

Implemented the P5 reframe pass in the authored sources only.

Changed:
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/front_matter.tex)
- [sections/01_related_work.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/01_related_work.tex)
- [sections/02_setup_and_assumptions.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/02_setup_and_assumptions.tex)
- [sections/05_comparison_with_ace_and_gaussian_benchmarks.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/05_comparison_with_ace_and_gaussian_benchmarks.tex)
- Appendix prose in sections 08, 09, and 10.

Addressed the routed findings by tightening the abstract theorem scope, separating the ordinary Borel statistic from the conditional represented-data correspondence, adding a fixed-code decision-problem subsection, translating the ACE comparison into concrete nuisance-rate regimes, qualifying upper-guarantee comparisons near the proposition, reframing the Gaussian result as a bounded-outcome diagnostic, shortening duplicated appendix summaries, and replacing the all-caps Appendix C normalization sentence.

Verification:
- Source grep passed for legacy cross-reference forms.
- Source grep found no ordinary prose hits for the flagged negative framing; the only remaining hit is the theorem-local verification-scope footnote, which is explicitly exempt.
- A temporary assembled manuscript compiled successfully with `latexmk` to a 65-page PDF. I did not edit `paper.tex` or `appendix_proofs.tex`.

Residual outside this rewrite pass: formal title arguments such as “Adaptive root-n minimaxity,” “Common Experiment Dichotomy,” and “Local Gaussian Benchmarks” were left unchanged because the prompt marked those statement-title findings outside scope and the formal layer is frozen.
