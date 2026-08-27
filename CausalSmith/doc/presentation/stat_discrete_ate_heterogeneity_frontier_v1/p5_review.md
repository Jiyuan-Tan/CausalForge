# Referee review

**Recommendation:** major_revision
**Overall score:** 6.6/10 — The formal contribution is substantial and mostly faithfully scoped, but the manuscript is not yet publication-ready because the exposition is overgrown, the bracket-versus-rate message needs sharper discipline, and several presentation/citation issues obscure the contribution.

The paper develops a finite-sample minimax bracket for ATE estimation with finite discrete adjustment, real outcomes under second-moment control, fixed overlap, and a known heterogeneity radius. The verified statements deliver a constructive known-radius upper bound, a same-class lower benchmark, endpoint reductions, and a precise localization of the residual shrinking-radius gap. The contribution is technically meaningful for high-dimensional discrete adjustment, but the manuscript needs substantial editing to make the statistical message, novelty boundary, and proof/verification interface digestible for econometrics readers.

## Strengths
- The main bracket is stated over one coherent real-outcome model class with arbitrary cell masses, fixed overlap, known scale, and known radius.
- The estimator construction usefully combines polynomial rare-cell estimation, collision estimation, and a deterministic known-radius selector.
- The paper is unusually explicit about endpoint regimes, fixed-positive-radius regimes, parametric elbows, and the residual shrinking-radius wedge.
- The verification appendix and contract give strong support that the displayed mathematical statements match the formal layer.

## Findings
- **[major·structure] global** — The main contribution is hard to evaluate because the manuscript presents many redundant restricted/all-alphabet theorem variants and lengthy proof machinery before the reader has a compact statistical picture of the result.
  - *Fix:* Restructure the paper so the main text contains the model, the two estimator ideas, the all-alphabet bracket, endpoint/regime interpretation, and a short proof roadmap; move restricted predecessor theorems and most proof-level algebra to an appendix or supplement.
- **[major·prose] intro** — Several high-level passages risk blurring the distinction between the delivered minimax bracket and exact minimax rates. For example, "The bracket has sharp implications across the named regimes" is accurate only when read with the matched-regime clauses and residual shrinking-radius wedge.
  - *Fix:* In the abstract, introduction, and discussion, consistently say that the paper establishes a bracket for all indices and exact-order rates in the named matched regimes; attach the residual-wedge qualifier whenever making global rate-sounding claims.
- **[major·structure] related work** — The closest-comparison discussion is useful but too long and partly proof-attribution focused; it does not yet isolate in one concise place exactly which rate, model, and estimator differences constitute the publishable econometric contribution.
  - *Fix:* Add a short dedicated comparison paragraph or table that states, in positive terms, the new real-outcome model, known-radius selector, upper benchmark, lower benchmark, and matched regimes relative to Zeng--Balakrishnan--Han--Kennedy; trim repeated surrounding narrative.
- **[major·structure] estimators and upper bounds** — The constructed estimators are mathematically explicit, but the paper gives no compact implementation-level pseudocode or minimal reproducibility artifact for the known-radius selector beyond dense formulas and an operation-count discussion.
  - *Fix:* Provide a concise algorithm box or supplementary implementation sketch for the aggregate polynomial branch, collision branch, and branch selection, with inputs \(n,d,M,\sigma,\epsilon\) and the returned statistic clearly specified.
- **[minor·prose] setup and assumptions** — The notation for lower benchmarks is needlessly fragile: the text uses \(\ell_{n,d,\sigma}\) for the capped converse benchmark in one place and then says the same symbol is local to the regime theorem for the triangular product benchmark.
  - *Fix:* Use \(\ell^{\mathrm{cap}}_{n,d,\sigma}\) and \(\ell^{\mathrm{tri}}_{n,d,\sigma}\) in theorem displays as well as prose, rather than relying on a local-symbol warning.
- **[minor·citation] related work** — The manuscript cites the nearest competitor as 2024, while the related-work brief identifies Zeng--Balakrishnan--Han--Kennedy as revised in 2026.
  - *Fix:* Check and update the bibliography entry and in-text description to identify the version whose results are being compared and formalized.
- **[minor·structure] related work** — Reader-facing prose contains unexplained formal-reference artifacts such as "\leanref{S-1}{real-outcome observational experiment with a finite discrete confounder}" and "\leanref{S-2}{binary-outcome discrete-confounder experiment}".
  - *Fix:* Either define the purpose and target of these Lean-reference annotations for journal readers or remove them from the prose and reserve formal crosswalk identifiers for the verification appendix.
- **[minor·prose] abstract** — The first display uses \(\mathcal P_{d,\epsilon,M,\sigma}\) before the symbol has a plain-word appositive.
  - *Fix:* At first use, write for example "over the radius-indexed model class \(\mathcal P_{d,\epsilon,M,\sigma}\)".
- **[nit·prose] intro** — The theorem map says "Four results carry the paper" and then lists the upper bound, lower bound, bracket, regime theorem, and endpoint proposition.
  - *Fix:* Change "Four results" to "Five results" or fold the endpoint proposition into the preceding sentence.

## Questions for authors
- Do the authors intend the submitted article to include the full formal proof audit, or will the journal version separate the statistical paper from the verification supplement?
- Which version of Zeng--Balakrishnan--Han--Kennedy is the formal comparison tied to, and did any 2026 revisions change the rate statements or conditions quoted here?
- Can the authors provide a minimal executable implementation or reproducible pseudocode for the selector, especially the aggregate polynomial branch?

