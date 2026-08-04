# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.1/10 — The paper delivers a coherent and verified minimax characterization with useful feasible finite-cell procedures, but a few presentation choices still obscure the contribution and could mislead readers about normalization and scope.

The paper studies honest confidence sets for transported complier contrasts when first stages are weak and target-to-source weights are dispersed. The verified statements support the central claim that the oracle and finite-cell expected-length frontier has order min{1,t0^{-1/2}} under the stated boundedness, overlap, domination, dispersion, and growth conditions. The contribution is technically meaningful for researchers working on transported IV, weak identification, and external validity with noncompliance, and the prose is mostly faithful to the formal layer.

## Strengths
- The main contribution is clear: the scalar n mu_n^2/kappa_n combines weak transported compliance and transport-weight dispersion in the expected-length frontier.
- The formal statements are carefully conditioned, and the prose generally preserves the verified theorem scope.
- The finite-cell and regular-cell procedures give constructive benchmarks rather than stopping at an oracle comparison.
- The related-work discussion situates the result well across LATE, weak-IV robust inference, and transportability.

## Findings
- **[minor·prose] Oracle Frontier and Score Inversion** — The definition of the score-inversion set writes the radius as "L_\alpha\left\{\frac1n\sum_{i=1}^n\frac{w(X_i)^2}{n}\right\}^{1/2}" before later explaining that it equals "L_\alpha\sqrt{\widehat\kappa_n/n}". The algebra matches the verified theorem, but the display is easy to misread as an unintended double normalization.
  - *Fix:* Rewrite the display directly as "L_\alpha\sqrt{\widehat\kappa_n/n}" after defining "\widehat\kappa_n=n^{-1}\sum_i w(X_i)^2", or write "L_\alpha\left\{n^{-1}\widehat\kappa_n\right\}^{1/2}" in the set definition.
- **[minor·citation] Related Literature and Discussion** — The discussion names several very recent or application-specific papers, for example "Ross2026", "Ren2025", "Rudolph2025", and "Aronow2026", but the manuscript excerpt does not give enough bibliographic context for a reader to assess exactly what results are being contrasted with the present minimax frontier.
  - *Fix:* Add one sentence for each cluster of recent papers specifying whether they address transported CACE identification, robust LATE inference, transported ATE efficiency/minimaxity, finite-population LATE intervals, or MTE extrapolation; keep the comparison tied to the present paper's established frontier and finite-cell constructions.
- **[nit·structure] global** — Some formal object titles use title case while surrounding prose uses sentence-style technical names, for example "Compact Causal Range", "Oracle Frontier Converse", and "Regular Cell Weight Attainment". This makes the manuscript read partly like a verification artifact rather than a journal article.
  - *Fix:* Use sentence-style titles for formal environments, for example "Compact causal range", "Oracle frontier converse", and "Regular cell weight attainment", unless the journal style requires title case.

## Questions for authors
- Can the feasible finite-cell procedures be accompanied by a brief implementation recipe or pseudo-code paragraph clarifying the data inputs used in practice?
- Are the 2025-2026 citations final published versions, working papers, or placeholders? The bibliography should make their status clear.

