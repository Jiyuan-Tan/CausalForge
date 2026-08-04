# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.1/10 — The paper delivers a coherent and formally verified minimax frontier result with useful feasible finite-cell constructions, while several exposition and positioning points still need tightening before publication.

The submission studies honest confidence sets for transported complier ratios under weak transported first stages and covariate-shift dispersion. The verified statements support the central claim: the oracle, fixed-geometry, uniform finite-cell, and regular finite-cell frontiers share the order \(\min\{1,t_0^{-1/2}\}\) under the stated compactness, overlap, transport, envelope, and growth conditions. The contribution is significant for readers working on weak-IV robust causal inference and external-validity problems, and the main remaining work is expository rather than mathematical.

## Strengths
- The paper identifies a clean effective-strength index, \(n\mu_n^2/\kappa_n\), that transparently combines first-stage weakness with transport-weight dispersion.
- The main minimax lower and upper bounds are matched and the feasible finite-cell procedures align with the oracle benchmark.
- The manuscript is unusually explicit about formal verification, assumptions, and the connection between the causal identification result and the statistical risk criterion.
- The related-work section now gives a clearer account of how the result relates to transported noncompliance, weak-IV robust LATE, and transported-ATE efficiency benchmarks.

## Findings
- **[minor·prose] Setup, Transport, and Honest Risk** — The receipt-contrast transport assumption is better motivated than before, but its empirical status remains partly ambiguous. The text says, "auxiliary target receipt evidence, such as linked dispensing records or a target-representative adherence validation sample, supplies design evidence for \cref{obj:ass:receipt-transport}," while the formal procedures use only target covariates. Readers need a sharper distinction between evidence used to justify the model restriction and data entering the confidence-set construction.
  - *Fix:* Revise the paragraph after \cref{obj:ass:receipt-transport} to state affirmatively that the statistical procedures condition on the model restriction and use the target covariate sample for weight learning, while separate target-side receipt evidence can be used at the design-validation stage to assess the target-average compliance equality. Give one compact template for what such evidence estimates and how it is compared to the transported source first stage.
- **[minor·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition still repeats the full inherited checklist from \(\mathcal P_n\). This is faithful, but it slows the reader and makes the single additional finite-cell restriction harder to see.
  - *Fix:* Keep the compact sentence "\(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\)" as the main definition, and move the expanded inherited checklist to a short auditability note or appendix table.
- **[minor·prose] Oracle Frontier and Score Inversion** — The role of the admissible-geometry assumption in \cref{obj:thm:oracle-score-inversion-attainment} is now mentioned, but the theorem still reads as though a global oracle procedure depends on selecting a particular geometry. The surrounding prose says, "The admissible-geometry hypothesis guarantees a deterministic covariate, weight, and propensity geometry in the ambient carrier for the comparison," which is helpful but should be made operational before the theorem statement.
  - *Fix:* Add one sentence before \cref{obj:thm:oracle-score-inversion-attainment} explaining that the construction is evaluated law-by-law using the oracle inputs, and the geometry assumption supplies nonempty admissible carrier structure for the formal comparison rather than an additional nuisance input used by the score rule.
- **[nit·prose] Related Literature and Discussion** — The closest-literature comparison is substantially improved, but the paragraph beginning "This positioning yields two direct scope statements" is dense and combines the transported-ATE and classical weak-IV comparisons in one place.
  - *Fix:* Split that paragraph into two shorter paragraphs, one for transported-ATE/minimax efficiency and one for weak-IV/two-sample IV. In each, state the delivered comparison in one affirmative sentence keyed to the parameter, assumptions, and frontier scale.
- **[nit·prose] global** — The manuscript uses both "least-favorable" and "least-favourable" in reader-facing titles and prose, for example \cref{obj:synth_5} uses "least-favourable" while \cref{obj:def:least-favorable-witness} uses "Least-favorable".
  - *Fix:* Standardize the spelling across titles, definitions, and surrounding prose.

## Questions for authors
- Can the design-validation discussion for \cref{obj:ass:receipt-transport} specify whether the auxiliary target receipt evidence is assumed external to the theorem or intended as part of an expanded empirical workflow?
- Do the authors want the finite-cell assumption checklist to remain in the main text for formal auditability, or can it be moved to the appendix to improve readability?

