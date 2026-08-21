# Referee review

**Recommendation:** major_revision
**Overall score:** 6.7/10 — The paper contains a substantial and carefully verified theoretical construction, but as written its organization, operational assumptions, and evidentiary support leave important publication-level clarity and usability gaps.

The submission develops contour-based instruments for partially linear models with fixed non-Gaussian cumulant separation and proves fixed-code root-n risk results under direct L1 treatment-code control. The verified formal layer appears to support the core mathematical claims, and the paper is careful about the ACE comparison being an upper-guarantee comparison. The main weaknesses are expository: key objects are used before being defined, the supplied-code and computation assumptions are hard to operationalize, and the paper gives little empirical or computational evidence for a very elaborate estimator.

## Strengths
- The core identification idea using MGF zeros and contour ratios is novel in the partially linear model setting.
- The main fixed-separation theorem is stated with explicit conditions and matched c/n and C/n MSE rates on fixed-code classes.
- The comparison with the published ACE guarantee is mostly framed honestly as an upper-bound comparison rather than estimator dominance.
- The manuscript includes useful explicit benchmarks, especially the symmetric mixture and Gaussian-Rademacher path.

## Findings
- **[major·structure] Main fixed-separation result** — Several central objects are invoked before their formal definitions appear, including the certified contour-bank handle, the search radius R1, and the adaptive contour estimator. For example, the main theorem says the statistic is that of obj:def:adaptive-contour-estimator, but that definition is deferred to Appendix C.
  - *Fix:* Move the contour-bank handle and adaptive estimator definitions, or a self-contained main-text version of them, before their first theorem-level use; leave only implementation details and proof support in the appendix.
- **[major·statement] Setup and assumptions** — The deterministic split is ambiguous because the paper writes observations as O_1,...,O_n but defines folds by i < floor(n/2) and i >= floor(n/2), which reads differently under one-based and zero-based indexing.
  - *Fix:* State the sample index set explicitly, preferably {0,...,n-1}, or redefine the folds in one-based notation; then check that all fold nonemptiness claims and empirical-process statements use the same convention.
- **[major·prose] Setup and assumptions** — The standalone code-radius assumptions are stated for every n, while the law classes and main fixed-code risk theorem use current-index code-radius gates. This makes the actual statistical assumption stronger or weaker depending on which passage the reader treats as operative.
  - *Fix:* Separate sequence-level bookkeeping assumptions from current-index class membership. State plainly that the fixed-code theorem uses the current epsilon_1,n L1 treatment-code gate, while all-index radius conditions are only imposed where explicitly named.
- **[major·prose] Main fixed-separation result** — The paper’s main theorem depends on a sufficiently accurate deterministic supplied treatment code, but the text gives little guidance on how such a code is obtained, verified, or related to ordinary first-stage learning. This is central to the economic and statistical interpretation of the result.
  - *Fix:* Add a focused discussion explaining admissible sources of supplied codes, whether they may be trained on auxiliary data or earlier folds, how the L1(P_X) gate should be interpreted, and how this assumption compares to nuisance-rate requirements in DML and ACE.
- **[major·other] Certified construction and executable correspondence** — The certified-computation layer is specified in detail, but the paper gives no executable artifact or numerical demonstration of the contour selector. For a method whose statistic is defined through a finite certified program, this leaves reproducibility and practical behavior difficult to assess.
  - *Fix:* Provide a minimal implementation or at least a simulation study for the symmetric mixture and Gaussian-Rademacher benchmarks reporting selected contours, denominator margins, fallback frequency, and empirical MSE. If no implementation is supplied, further downweight the computational language in the abstract and introduction.
- **[minor·prose] abstract** — The sentence “the same statistic controls the generalized lower (1-gamma)-quantile of absolute error by order (gamma n)^(-1/2)” is formally precise but easy to misread as a conventional high-probability guarantee, whereas gamma > 1/2 makes this a lower-tail quantile criterion.
  - *Fix:* Add a short affirmative clarification at first mention, such as: “at the lower-tail level 1-gamma defined below, the generalized inverse is bounded at order ...”.
- **[minor·citation] Related work** — The related-work section cites the DML and semiparametric literature but gives the closest direct comparison mainly for ACE. Readers need a sharper account of what the contour result adds relative to residualized Robinson/DML estimators under comparable nuisance-code assumptions.
  - *Fix:* Add a short comparison paragraph or table stating the DML, ACE, and contour targets, required nuisance conditions, non-Gaussian conditions, and delivered risk criteria on the common partially linear problem.
- **[minor·statement] Explicit mixture reductions and local benchmarks** — The theorem titled “Local Gaussian Benchmarks” contains the phrase “the Gaussian--Rademacher path benchmark conclusion holds” rather than restating the substantive conclusion in that formal environment. This makes the theorem less self-contained for readers.
  - *Fix:* Restate the actual risk and denominator conclusions in the theorem or make the theorem explicitly a corollary of the preceding lemma with a precise cross-reference.
- **[nit·prose] abstract** — ACE is used in the abstract before being expanded or identified.
  - *Fix:* Expand or identify ACE at first use in the abstract and again in the introduction if needed.

## Questions for authors
- How do the authors envision practitioners obtaining or certifying the deterministic L1(P_X) treatment-code radius used by the fixed-separation theorem?
- Is the lower (1-gamma)-quantile criterion intended as a primary finite-sample performance metric, or mainly as the metric needed for comparison with the JMS ACE result?
- Will the authors provide a runnable implementation of the contour selector, or should the certified-computation contribution be read solely as a formal interface specification?

