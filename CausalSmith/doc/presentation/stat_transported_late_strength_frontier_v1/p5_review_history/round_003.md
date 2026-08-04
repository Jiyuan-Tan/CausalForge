# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results deliver a coherent and useful minimax characterization, with only localized prose and positioning issues remaining before publication-quality presentation.

The paper studies honest confidence sets for transported complier effects in two-sample encouragement designs and characterizes the minimax expected-length frontier through the effective strength n mu_n^2/kappa_n. The main oracle, fixed-geometry, and finite-cell feasible results are significant and, under the verification contract, are faithfully represented in their formal statements. The manuscript is close to publishable, but a few prose passages still frame scope through non-coverage or rely on imprecise bibliographic positioning.

## Strengths
- The effective-strength scalar n mu_n^2/kappa_n is a clean and useful synthesis of weak first stages and transport-weight dispersion.
- The compact causal range resolves the usual unbounded-ratio expected-length difficulty in a way that is central to the paper's criterion.
- The oracle lower and upper bounds, fixed-geometry result, and feasible finite-cell constructions form a coherent progression from benchmark theory to constructive procedures.
- The prose generally tracks the verified theorem conditions and avoids overstating finite-sample or semiparametric claims.

## Findings
- **[minor·prose] Fixed Geometry and Feasible Cell Weight Learning** — The sentence "These constructions are minimax attainability benchmarks under the theorem's growth gates; unknown cell structures and propensities remain outside the construction" states non-coverage outside a labelled limitations or future-work section, contrary to the manuscript's own reader-facing prose contract.
  - *Fix:* Rewrite affirmatively, for example: "These constructions are minimax attainability benchmarks for designs with known cell partitions and, in the regular-cell case, known source-cell probabilities and propensities."
- **[minor·prose] Oracle Frontier and Score Inversion** — The sentence "the transported frontier extends the usual weak-IV expected-length scaling rather than changing its exponent" frames the contribution by negation and could be read as a broader claim about all transported weak-IV settings than the verified no-shift and fixed-geometry statements establish.
  - *Fix:* State the positive scope directly, for example: "With w=1, the fixed-geometry value has the same inverse-square-root effective-strength order as the compact weak-ratio benchmark."
- **[minor·citation] Related Literature and Discussion** — The discussion lists very recent works such as "Ross2026", "Rudolph2025", "Aronow2026", and "Ren2025" and asserts their publication or working-paper status, but the manuscript excerpt still gives readers little information about the specific estimands, assumptions, or results being contrasted.
  - *Fix:* Add one clause per cluster identifying the relevant result being used for comparison, and ensure the bibliography entries include full publication status, venue or working-paper source, and version/date where applicable.
- **[nit·prose] abstract** — The abstract states "The converse is already witnessed by a unit-transport-weight geometry" without briefly indicating that this is a least-favorable submodel argument inside the stated model classes. The sentence is accurate but compressed enough that readers may miss why a no-shift geometry proves a transported lower bound.
  - *Fix:* Revise to "The lower bound is witnessed by a unit-transport-weight submodel, while the attaining score-inversion bound uses t_n to combine first-stage strength and weight dispersion."

## Questions for authors
- Can the bibliography give stable version information for the 2025-2026 working papers so readers can verify the exact comparison set?

