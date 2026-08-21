# Holistic revision pass 2

- mode: reframe
- source digest before: `3cec4a1e174c4b17c277d8241a7f5923d1d1c681b3c3dfaf6eeb8ebb5a83577e`
- source digest after: `8c208c605ea1fc65ea58ec476c23d7a22b557e74dab5c90cf58825c22a3e3a94`

## Reviser report

Implemented the final P5 reframe pass in the authored sources only.

Changed:
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/front_matter.tex)
- [sections/01_related_work.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/01_related_work.tex)
- [sections/04_main_fixed_separation_result.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/04_main_fixed_separation_result.tex)
- [sections/05_comparison_with_ace_and_gaussian_benchmarks.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/05_comparison_with_ace_and_gaussian_benchmarks.tex)
- [sections/06_explicit_mixture_reductions_and_local_benchmarks.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/06_explicit_mixture_reductions_and_local_benchmarks.tex)
- [sections/10_appendix_c_certified_construction_and_executable_correspondence.tex](<repo-root>/CausalSmith/doc/presentation/stat_sa_plm_cumulant_converse_nongaussian_spectral_annihilation/sections/10_appendix_c_certified_construction_and_executable_correspondence.tex)

Addressed:
- Split and reframed the abstract around the statistical theorem, ACE comparison, benchmarks, and conditional reproducibility layer.
- Replaced the dense first-page roadmap table with a prose theorem hierarchy.
- Foregrounded fixed-code conditioning immediately before the main theorem, including post-training conditioning.
- Tightened ACE language to an upper-bound comparison on the common clipped-code class.
- Removed remaining `\leanref` references from reader-facing prose.

Verification:
- Temporary authored-source PDF build passed with `latexmk`.
- Scans found no legacy `\ref`, `\eqref`, or `\autoref`.
- Prose-contract scan leaves only the theorem-local verification footnote, which is the exempt generated disclosure.

No routed finding was declined. I left the title-case formal environment titles unchanged because that issue was listed as outside this pass and the formal layer is frozen.
