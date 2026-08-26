# Referee review

**Recommendation:** major_revision
**Overall score:** 6.8/10 — The paper appears to deliver a technically meaningful verified minimax bracket, but publication in its current form is held back by trust-boundary prose, readability, and positioning issues.

The submission studies finite-sample ATE estimation with a finite discrete adjustment variable, real outcomes, fixed overlap, bounded conditional means and second moments, and a known heterogeneity radius. It constructs polynomial and collision estimators, combines them with a known-radius selector, and proves a same-class upper/lower minimax bracket with matched regimes and an explicitly isolated shrinking-radius wedge. The verified statements support the main mathematical claims, but the manuscript needs substantial revision to make the contribution, verification scope, and relation to prior work clear enough for a leading econometrics audience.

## Strengths
- The model class and loss criterion are stated precisely, including overlap, scale, moment, and heterogeneity-radius conditions.
- The main results are constructive on the upper side and same-class on the lower side, with clear endpoint and matched-regime consequences.
- The manuscript is unusually explicit about estimator definitions, embeddings, and verification artifacts.
- The residual shrinking-radius region is presented honestly as an open frontier rather than as a solved exact minimax rate.

## Findings
- **[major·prose] global** — The verification/trust-boundary prose is stale or too broad relative to the current contract. The author footnote says, "where a result from the literature is a formal dependency, it enters as a published input rather than a Lean-checked step," while the current verification contract records no `external_dependencies` for the listed paper objects and records the binary source lemmas as checked declarations with faithful proof audits.
  - *Fix:* Revise the author footnote and verification note to say exactly which displayed statements are Lean-checked in the current artifact, which proposition is conditional on the displayed published binary collision guarantee, and that citations otherwise provide attribution and statistical context. Remove wording that suggests the main bracket relies on undisclosed published inputs unless such theorem-local dependencies are actually present and footnoted.
- **[major·structure] Clarity & presentation** — The manuscript is difficult to read as an econometrics paper because the main line is buried under long formal statements, repeated restricted/all-alphabet variants, and proof-mechanics detail. A reader must work hard to distinguish the central bracket from auxiliary transport packages, source lemmas, and legacy restricted-range results.
  - *Fix:* Restructure the exposition around one main theorem, one endpoint corollary, and one regime theorem in the main text; move restricted predecessor theorems and low-level covariance/transport statements to an appendix or supplement; add a short roadmap explaining which results are central and which are auxiliary.
- **[major·prose] Main bracket and matched regimes** — The contribution is a bracket with exact-order matching only in named regimes, while the shrinking-radius wedge remains open. Although the prose generally states this, the title and some high-level phrasing such as "Minimax average treatment effect estimation" and "main rates" can be read as claiming a complete minimax characterization over all radii.
  - *Fix:* Sharpen the title or first-paragraph framing to use "minimax bracket" or "minimax bounds" and state early that exact-order characterization is obtained at the endpoints, fixed positive radii, saturation, and elbow regimes, with a residual shrinking-radius frontier isolated separately.
- **[minor·citation] Related work** — The related-work section is broadly adequate but underplays some econometric efficiency and causal-inference references that are directly relevant to the setup. The provided context includes Hirano, Imbens, and Ridder (2003) and Hernán and Robins (2020), but the manuscript does not incorporate them into the early positioning.
  - *Fix:* Add the missing efficiency and causal-inference references where the semiparametric ATE benchmark is discussed, and distinguish clearly between fixed-dimensional efficient estimation, high-dimensional nuisance estimation, and the paper's finite discrete arbitrary-cell-mass minimax problem.
- **[minor·other] Estimators and upper bounds** — The polynomial estimator is mathematically specified, but the practical implementation description is too terse for a reader to reproduce the aggregated statistic confidently, especially the falling-factorial one-mark terms and the post-aggregation operation count.
  - *Fix:* Add pseudocode or a short implementation appendix mapping the ordered-tuple formula to count/totals/falling-factorial arrays, including how zero counts and clipping are handled.
- **[minor·structure] Main bracket and matched regimes** — The regime table is useful but purely textual; the geometry of the matched regions and the residual wedge is central to the paper and currently hard to visualize.
  - *Fix:* Add a schematic phase diagram in the \((d,\sigma)\) scale, marking exact homogeneity, fixed positive radii, saturation, parametric-dominance elbows, and the residual shrinking-radius wedge.
- **[nit·prose] global** — Some prose repeats the same definitions and benchmark formulas many times, which creates notation fatigue and increases the chance of inconsistencies between \(u_{n,d}\), \(h_{n,d,\sigma}\), \(r_{n,d,\sigma}\), \(q_{n,d,\sigma}\), and \(\ell_{n,d,\sigma}\).
  - *Fix:* Define the benchmark notation once in the setup, refer back to it consistently, and remove duplicated formula blocks except where restatement is essential for a theorem to be readable.

## Questions for authors
- Is the final intended formalization scope that all source lower lemmas used in the main bracket are Lean-checked, with Zeng et al. serving only attribution/context, except for the explicitly conditional binary collision comparison?
- Can the authors provide a minimal reference implementation of the selector and polynomial branch, or is the estimator intended only as a mathematical construction?
- Do the authors view closing the shrinking-radius wedge as necessary for the paper's intended claim, or is the bracket plus matched-regime characterization the final target contribution?

