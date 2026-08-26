# Referee review

**Recommendation:** major_revision
**Overall score:** 7.4/10 — The paper contains a strong and apparently delivered theoretical contribution, but several exposition and scope-control issues need repair before it reads as a reliable econometrics submission.

The submission establishes a sharp fixed-interior minimax rate for finite-alphabet ATE estimation under unrestricted discrete confounding and fixed overlap, using a computable ratio-polynomial hybrid estimator and a lower-bound transfer from Zeng et al. The main contribution is significant: it closes the logarithmic upper-bound gap left by the closest causal benchmark in the calibrated range. The verified statements support the central theorem, but the manuscript needs clearer proof conventions, tighter scope qualifiers in stand-alone prose, and more accessible positioning and implementation exposition.

## Strengths
- The central rate result is important and directly addresses a known open logarithmic gap in discrete-covariate causal minimax theory.
- The estimator is constructive, universally tuned across fixed interior overlap levels, and tied to a clear heavy/light sparse-cell decomposition.
- The paper is unusually explicit about theorem dependencies and includes theorem-local verification-scope disclosures for the imported lower-bound ingredient.
- The related-work section identifies the closest predecessor and states the key rate comparison rather than citing it generically.

## Findings
- **[major·prose] appendix/proofs and minimax-risk definition** — Several proof passages use a nonstandard supremum convention, for example: "If that family is not bounded above, the real-valued supremum is again 0." Under ordinary mathematical convention, an unbounded nonnegative family has supremum +infinity, and a reader cannot infer the Lean totalization convention from the minimax-risk definition.
  - *Fix:* Rewrite the affected proof passages using ordinary extended-real suprema, or state the paper's totalized order convention explicitly near the minimax-risk definition and explain why the relevant experiment classes and estimator risks are bounded in the displayed applications. Prefer the former where n>0 and d>0 make the class inhabited and the estimators are bounded or have finite risk.
- **[minor·prose] related work and discussion** — Some stand-alone summaries of the main result omit the calibrated range and large-sample conditions. For example, "The present paper constructs a computable balanced ratio-polynomial hybrid estimator that attains this lower scale in the fixed-interior overlap regime" should also carry the verified conditions n >= N_epsilon and d <= rho_epsilon n log n.
  - *Fix:* Add the calibrated range and sufficiently-large-n qualifier to each self-contained rate summary, especially in Related work and Discussion, so the positive scope matches the theorem whenever the sentence is read outside the theorem display.
- **[minor·prose] main results** — The sentence "The operation count is polynomial in the degree M(n) and linear in the alphabet size d, so the construction is an explicit count-based procedure rather than an existential minimax rule" uses contribution-by-negation outside a limitations section.
  - *Fix:* Rewrite affirmatively, e.g. "The operation count is polynomial in M(n) and linear in d, giving an explicit count-based procedure with the stated risk certificate."
- **[minor·citation] related work** — The comparison with Zeng et al. gives the main upper and lower rates, but it would be more useful to econometrics readers if it also summarized their same-sample equivalence of plug-in, IPW, and doubly robust estimators and the resulting consistency benchmark for those standard estimators.
  - *Fix:* Add a compact paragraph or table contrasting: standard estimator class, Zeng et al. upper scale d^2/n^2 + 1/n, their lower scale d^2/(n^2 log^2 n) + 1/n, and this paper's hybrid upper scale in the calibrated fixed-interior range.
- **[minor·structure] setup and assumptions** — The hybrid estimator definition is mathematically complete but difficult to implement from the main text because the coefficient construction is hidden inside the polynomial expansion and the sparse-arm coefficient formula appears later in the appendix.
  - *Fix:* Add a short algorithm box after the estimator definition: compute pilot counts, classify categories, evaluate the ratio branch, compute g_{M,j} by recurrence or closed form, evaluate sparse-arm factorial moments, sum light and heavy contributions, and truncate.
- **[nit·prose] abstract** — The phrase "calibrated fixed-interior range" is accurate but opaque in a page-facing summary unless the reader recalls the preceding display and the epsilon-dependent constants.
  - *Fix:* Use a more explicit phrase such as "within the range n >= N_epsilon and d <= rho_epsilon n log n for fixed epsilon in (0,1/2)."

## Questions for authors
- Can the paper report or bound the numerical cutoff N0 and the practical size of the universal tuning constants used by the hybrid estimator?
- Will the authors provide reference code or pseudocode for computing the Chebyshev reciprocal coefficients and the factorial-moment light branch?
- Can the lower-bound transfer from Zeng et al. be stated as a named cited lemma in the main text before the sharp minimax theorem, so readers see exactly which published input supplies the lower side?

