# Referee review

**Recommendation:** major_revision
**Overall score:** 6.5/10 — The paper has a credible and potentially useful verified minimax bracket, but the manuscript substantially overburdens the reader with proof-interface material, stale verification-boundary prose, and several presentation choices that obscure the economic and statistical contribution.

The submission studies finite-sample ATE estimation with a discrete adjustment variable, arbitrary cell masses, fixed overlap, bounded real-outcome moments, and a known heterogeneity radius. It constructs polynomial and collision estimators, combines them by a radius-aware selector, and proves a same-class all-alphabet upper/lower minimax bracket with matched regimes outside a residual shrinking-radius wedge. The contribution is interesting, but the paper as written needs major revision for exposition, stale verification-scope claims, and tighter positioning against the closest binary discrete-adjustment literature.

## Strengths
- The main bracket is stated over the same real-outcome model class on both upper and lower sides, which is an important strength.
- The known-radius selector gives a constructive upper benchmark with clear polynomial, collision, and clipped-zero branches.
- The paper honestly identifies the residual shrinking-radius wedge as open in the Future work and Limitations sections.
- Endpoint and regime results help interpret when the bracket is rate tight.

## Findings
- **[major·prose] global** — The manuscript contains stale trust-boundary prose suggesting that some literature results enter as unverified formal dependencies, while the verification contract lists no external_dependencies and marks the source-interface statements as checked with faithful proofs. Offending sentence: "where a result from the literature is a formal dependency, it enters as a published input rather than a Lean-checked step".
  - *Fix:* Revise the author footnote and verification note to say that the displayed formal statements are Lean-checked at the cited commit, while citations provide attribution and statistical context; remove language saying literature results enter as maintained assumptions unless a current theorem-local external dependency actually exists.
- **[major·structure] global** — The paper is not publishable in its current form as an econometrics article because the appendices include very long proof transcripts and implementation-level formal-audit prose that swamp the statistical argument. This makes it difficult to distinguish the contribution, proof strategy, and verification metadata.
  - *Fix:* Move low-level Lean proof transcripts and proof-audit mechanics to a separate online verification appendix or artifact; keep in the manuscript a conventional mathematical proof sketch for each main ingredient and a concise reproducibility appendix with commit, toolchain, and build command.
- **[major·prose] intro** — The introduction explains the bracket but does not clearly state early enough that the main minimax result is a bracket with an unresolved shrinking-radius gap, not a full minimax rate uniformly over all radii. The residual wedge is described later, but the contribution statement can be read as a complete frontier result.
  - *Fix:* In the first contribution paragraph, state affirmatively that the paper establishes a constructive upper benchmark and same-class lower benchmark, identifies matched endpoint/fixed-radius/elbow regimes, and characterizes the remaining shrinking-radius wedge as the open frontier.
- **[major·citation] related work** — The nearest comparison to Zeng, Balakrishnan, Han, and Kennedy is broadly accurate, but it does not give enough concrete side-by-side conditions and rates in the main related-work section for a reader to assess novelty without reading the later discussion.
  - *Fix:* Add a compact paragraph or table in Related work comparing outcome type, heterogeneity radius, known-radius use, cell-mass assumptions, upper rate, lower rate, and matched regimes against Zeng--Balakrishnan--Han--Kennedy.
- **[major·structure] estimators and upper bounds** — The polynomial estimator is mathematically specified but not operationally transparent. A reader is told there is a post-aggregation program with polynomial operation count, but the estimator remains hard to implement from the displayed formula.
  - *Fix:* Provide pseudocode or a short implementation-level description showing the sufficient cell aggregates and recurrence used to compute the factorial terms, and separate that from the formal ordered-index display.
- **[minor·prose] abstract** — The abstract introduces \(\sigma\) as both a radius parameter and a scalar radius but uses the symbol before fully orienting the reader to its role. The first-use gloss is close but still syntactically awkward: "for the radius parameter \(\sigma\)".
  - *Fix:* Rewrite the first occurrence as "a known radius parameter \(\sigma\), which bounds the maximal cell-effect deviation by \(\sigma M\)" or use words until the setup section.
- **[minor·structure] discussion, extensions, and limitations** — The Binary collision comparison subsection is late relative to its importance for positioning against the nearest competitor.
  - *Fix:* Move the comparison, or at least its rate table and interpretation, into Related work or the end of the Introduction; keep the formal conditional proposition in the discussion or appendix.
- **[minor·prose] global** — Several theorem and subsection titles are close to technical labels rather than reader-facing statistical claims, for example "Fixed-radius wedge characterization" and "All-d radius converse".
  - *Fix:* Rename reader-facing titles to concise sentence-case descriptions that identify the statistical content, such as "Matched regimes and the shrinking-radius wedge" and "Radius-sensitive lower bound".
- **[minor·prose] setup and assumptions** — The knownness of \(M\) and \(\sigma\) is central to the estimator class and selector but is not emphasized when the minimax experiment is introduced.
  - *Fix:* Add one sentence before the estimator section stating that the risk benchmark and selector are indexed by known \(M\) and known \(\sigma\), with the latter entering the deterministic branch choice.
- **[minor·prose] global** — Notation alternates between \(u_{n,d}\) and apparent typo forms in the verification-derived text such as \(\nu_{n,d}\) in several statements, which would confuse readers if it appears in the compiled manuscript.
  - *Fix:* Audit all occurrences of \(\nu_{n,d}\) versus \(u_{n,d}\) and standardize the polynomial scale notation throughout the manuscript and tables.
- **[nit·prose] global** — The text repeatedly uses internal labels such as "handle," "source-interface," and "certificate" in reader-facing prose.
  - *Fix:* Reserve these terms for the verification appendix and use statistical names in the main text, such as calibration constants, embedded hard family, and transfer lemma.

## Questions for authors
- Can the main text include a concise example regime, such as \(d\asymp n\), showing how the selector and lower benchmarks differ as \(\sigma\) shrinks?
- Is the known-radius assumption intended as a modeling primitive, an oracle benchmark, or a stepping stone toward adaptation?

