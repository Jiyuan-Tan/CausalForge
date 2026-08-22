# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.1/10 — The paper delivers a sharp and useful minimax characterization with verified formal statements, but several presentation and claim-fidelity repairs are needed before publication.

The submission establishes a finite-population minimax MSE frontier for low-order polynomial network interference under common Bernoulli assignment, with matching clipped-SNIPE upper bounds, complete-block lower bounds, an exact complete-block local linear benchmark, and a fair-coin specialization. The contribution is significant for design-based network experiments because it turns local Bernoulli contrast geometry and neighborhood overlap into a transparent rate. The formal statements are supported by the verification contract, and the prose mostly tracks the theorem scope, but the manuscript needs targeted repairs in notation, verification-scope wording, and a few interpretive phrases.

## Strengths
- Sharp bounded-class minimax frontier with both coefficient-mass and uniformly bounded-outcome formulations.
- Clear separation of local score energy A_d and the graph overlap factor d, yielding an interpretable design benchmark.
- Strong exact complete-block and local linear benchmark results that clarify where SNIPE is optimal and how the constants arise.
- Related work section appears early and engages the closest SNIPE antecedent directly.

## Findings
- **[minor·statement] main results** — The bounded-outcome frontier theorem introduces an undefined perturbation notation: "\(\delta=\operatorname{tilt}_{\beta,p}(B,m,d)\)." Earlier the manuscript defines \(\delta(n,d,\beta,B,p)\), while the verified declaration uses the corresponding tilt-amplitude object.
  - *Fix:* Use one notation consistently. The simplest fix is to replace this display with \(\delta=\delta(n,d,\beta,B,p)\) and, if desired, add a parenthetical that this is the tilt amplitude defined in \cref{obj:def:block-family}.
- **[minor·prose] title/verification note** — The author footnote says, "results cited from the literature enter as published inputs," while the verification note and current contract record no external formal dependencies for the displayed objects. This creates a stale trust-boundary description.
  - *Fix:* Revise the footnote to match the current verification scope, for example: "The displayed formal statements and proofs are Lean-verified; cited literature supplies econometric framing and positioning." Keep the verification note's statement about no external formal dependencies.
- **[minor·prose] discussion and extensions** — The sentence "the assignment probability determines which orders are visible through the coefficients \(\Delta_r(p)\)" risks suggesting observability of coefficient orders. The fair-coin scope is narrower: even-order centered contrasts drop out of the all-treated-versus-all-control representer.
  - *Fix:* Replace "which orders are visible" with a representer-specific phrase, such as "which orders enter the all-treated-versus-all-control Bernoulli representer through \(\Delta_r(p)\)."
- **[minor·prose] setup and assumptions** — In \cref{obj:def:block-family}, the schedule is defined for active-block subsets with \(|T|\le k_\star\), followed by "All coefficients for subsets not contained in the active block, and all coefficients of inactive units, are zero." The text leaves active-block subsets with \(|T|>k_\star\) implicit.
  - *Fix:* Add a sentence stating that all remaining active-block coefficients, including subsets with \(|T|>k_\star\), are zero. This makes the construction immediately reproducible from the manuscript.
- **[nit·structure] main results** — The logical-role table manually bolds labels such as "Upper bound" and "Lower bound" but has no table number or caption, making it harder to reference later.
  - *Fix:* Convert the display to a numbered table with a short caption, or introduce it as an unnumbered roadmap and avoid later dependence on it.
- **[nit·citation] related work** — The related-work discussion is adequate on the closest SNIPE paper, but the opening design-based lineage is narrower than the context supplied to the authors; Fisher's randomization logic, Cox's interference discussion, Rosenbaum's randomization tests, and Toulis and Kao's peer-influence estimands are natural nearby references.
  - *Fix:* Add a compact sentence in the first two related-work paragraphs acknowledging these strands, while keeping the focus on the closest low-order SNIPE and minimax comparison.

## Questions for authors
- Do the authors intend the paper-facing verification statement to assert that the displayed results have no external formal dependencies, as the current contract indicates?
- Will the replication artifact expose the Lean declarations by theorem label so that readers can map \cref{obj:...} objects to the checked statements?

