# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.2/10 — The paper delivers a sharp and interesting minimax benchmark with strong formal support, but a few presentation choices still make the scope and practical meaning of some claims easier to overread than they should be.

The paper studies ATE estimation with binary treatment/outcome and an unrestricted growing discrete covariate alphabet under overlap. Its main contribution is a sharp fixed-interior minimax rate, achieved by a computable heavy/light hybrid estimator and matched to an imported lower-bound construction. The verified statements support the central mathematical claims, and the manuscript is largely careful about the endpoint and triangular-array limitations. I would recommend publication after minor revisions to tighten scope, implementation wording, and positioning.

## Strengths
- The main rate statement is important: it identifies the logarithmic improvement and the parametric and consistency regimes for unrestricted discrete confounding.
- The heavy/light estimator is constructive and well matched to the statistical difficulty of sparse categories.
- The manuscript is unusually precise about the verification boundary and correctly marks the imported lower-bound dependency.
- The endpoint result at exact randomization is clearly separated from the fixed-interior theory.

## Findings
- **[minor·prose] title/abstract/main results** — The title and a few high-level phrases can still be read as a global characterization over all alphabet sizes and overlap sequences. The title, "Sharp Minimax Rates for Average Treatment Effects with Unrestricted Discrete Confounding," is broader than the verified fixed-interior result, which requires fixed 0<epsilon<1/2, n>=N_epsilon, and d<=rho_epsilon n log n, plus a separate endpoint bracket at epsilon=1/2.
  - *Fix:* Either revise the title/subtitle to signal the fixed-interior calibrated range, or add one explicit sentence at the end of the abstract and introduction saying that the paper does not characterize the minimax risk outside d<=rho_epsilon n log n or for triangular arrays epsilon_n -> 1/2.
- **[minor·prose] main results/discussion** — The selected near-randomization estimator is described as a useful envelope, but it depends on epsilon and on the unspecified fixed-interior constant C_epsilon. This is a valid theoretical selector, but the prose could make it sound like an immediately implementable adaptive procedure.
  - *Fix:* Call it a deterministic comparison or oracle-calibrated selector, and state explicitly that the paper does not provide a data-driven adaptive rule for unknown epsilon or unknown C_epsilon.
- **[minor·statement] setup and assumptions** — The small-sample conventions remain slightly under-specified. Definition 7 says that for n<N0 the estimator uses the ratio branch on every category, while some displayed formulas involve m1 and log n; the theorem also states computability for every n,d in N. If N includes zero, the written formulas appear to involve zero denominators or undefined logarithmic conventions.
  - *Fix:* State at the start of the statistical setup that n>=1 and d>=1 throughout, or add explicit conventions for n=0 and m1=0; then align the computability clause with that convention.
- **[nit·prose] positioning** — The comparison with Zeng, Balakrishnan, Han, and Kennedy is mostly accurate but could be sharper about what is imported and what is new. The current text says the lower-bound scale is transferred from their construction, but does not state in one place that the new contribution is the matching computable upper bound and the resulting sharp regimes.
  - *Fix:* Add a short positioning paragraph or sentence in the introduction: Zeng et al. provide the fixed-sample lower-bound ingredient and analyze standard estimators; this paper closes the upper-bound gap by constructing the hybrid estimator and deriving the sharp fixed-interior rate.
- **[nit·structure] appendix** — The appendix proofs contain many verification-oriented details, including Lean declaration comments and repeated empty-class/supremum convention arguments. These are rigorous, but they sometimes obscure the statistical structure of the proof.
  - *Fix:* Move most Lean declaration comments and purely formal convention checks to the verification note or footnotes, while leaving the main appendix proofs focused on the heavy/light decomposition, approximation bias, variance control, and minimax reduction.

## Questions for authors
- Is the selected near-randomization rule intended only as a theoretical envelope, or do you intend readers to implement it with explicit or estimable constants?
- Can you provide even rough numerical guidance on the calibration constants N_epsilon and rho_epsilon, or should readers view the result as purely asymptotic?

