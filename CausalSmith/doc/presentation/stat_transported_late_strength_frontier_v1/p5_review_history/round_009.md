# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results deliver a clean and useful minimax frontier, but a few prose and presentation choices still obscure the exact scope of the contribution.

The paper characterizes honest expected-length frontiers for transported complier ratios under weak transported first stages and covariate-shift dispersion. The formal statements, as summarized in the verification contract, support the main oracle, fixed-geometry, and finite-cell attainment claims. The contribution is publishable after targeted revision to sharpen interpretation of the receipt-transport assumption, clarify related-work positioning, and reduce some reader-facing redundancy.

## Strengths
- The main frontier indexed by \(n\mu_n^2/\kappa_n\) is conceptually clear and important for transported IV designs with noncompliance.
- The paper gives matched lower and upper bounds, plus feasible finite-cell constructions, rather than only an oracle benchmark.
- The verified theorem statements appear faithfully represented in the main mathematical claims.
- The compact causal range is used effectively to separate this problem from unbounded weak-ratio impossibility results.

## Findings
- **[minor·prose] Setup, Transport, and Honest Risk** — The practical content of receipt-contrast transport remains somewhat underdeveloped. The paragraph after the assumption gives an example and diagnostic, but the reader is still left to infer what sampling or design evidence justifies the target-average equality when the formal two-sample theorem observes only target covariates.
  - *Fix:* Add a short, explicit paragraph stating that the target covariate sample is the statistical input used by the procedures, while the receipt-transport equality is a design/model restriction supported by external target adherence or receipt evidence; distinguish this from a theorem-provided target receipt sample.
- **[minor·structure] Fixed Geometry and Feasible Cell Weight Learning** — The theorem title "Finite-cell weight attainment" understates and slightly misdirects the result: the verified theorem establishes sample-only score-inversion attainment using target empirical frequencies and a collision-scale dispersion proxy, not merely weight attainment.
  - *Fix:* Rename the theorem to something like "Finite-cell sample-only score-inversion attainment" or "Finite-cell feasible score-inversion frontier" and adjust the surrounding first sentence accordingly.
- **[minor·prose] Related Literature and Discussion** — The closest-literature comparison still compresses several distinct comparisons into dense paragraphs, making the novelty claim harder to audit against Chen and Huang, Rudolph and van der Laan, Ross, Choi et al., Ma, and Smucler et al.
  - *Fix:* Split the closest-literature discussion into two short paragraphs: one on transported noncompliance/CACE and one on weak-IV-robust or two-sample IV inference; end each with the specific positive scope added by this paper.
- **[minor·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the entire inherited assumption list from \(\mathcal P_n\), which is faithful but slows the reader and obscures the single additional finite-cell restriction.
  - *Fix:* Keep the formal checklist if needed for auditability, but precede it with a compact definition sentence saying \(\mathcal N_n=\{P\in\mathcal P_n: \cref{obj:ass:finite-cell-source}\}\); move the expanded inherited checklist to a parenthetical or appendix table.
- **[nit·prose] Oracle Frontier and Score Inversion** — The oracle score attainment theorem includes an "Admissible geometry" assumption whose role is not explained in the surrounding prose, even though the result is presented as a global oracle construction over \(\mathcal P_n\).
  - *Fix:* Add one sentence after the theorem explaining that this assumption guarantees an admissible deterministic geometry in the ambient carrier for the comparison, while the score-inversion procedure is evaluated using each law's oracle weight and propensity.

## Questions for authors
- In applications, what concrete target-side evidence is expected to justify the averaged receipt-transport equality when the theorem's feasible procedure observes only target covariates?
- Do the authors intend the finite-cell procedures primarily as implementable methods for discretized covariates or as sharp attainability benchmarks for the frontier?

