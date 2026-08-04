# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The verified formal contribution is strong and coherent, but the manuscript still needs sharper positioning and several prose repairs before it would read as a publishable econometrics submission.

The paper characterizes honest expected-length frontiers for transported complier-effect ratios under bounded outcomes, fixed instrument overlap, transport domination, controlled weight dispersion, and finite-cell growth conditions. The verified statements support the central minimax order claim and the oracle and finite-cell constructions. The main remaining weaknesses are expository and positioning-related: the paper needs clearer literature contrasts, better motivation for its relatively specialized assumptions, and a few wording changes to keep interpretation exactly aligned with the formal scope.

## Strengths
- The central effective-strength index \(t_n=n\mu_n^2/\kappa_n\) is a clean and useful synthesis of weak first stages and transport-weight dispersion.
- The verified theorem suite delivers matching lower and upper expected-length orders for the oracle benchmark and constructive finite-cell procedures.
- The compact parameter-space treatment usefully distinguishes this problem from unbounded weak-ratio settings where expected length can be pathological.
- The manuscript is unusually explicit about model restrictions, procedure classes, and risk criteria.

## Findings
- **[major·citation] Related Literature and Discussion** — The discussion lists very recent works such as "Ross2026", "Rudolph2025", "Aronow2026", and "Ren2025" and summarizes them only at a broad topic level. Readers cannot tell which estimands, sampling structures, weakness regimes, transport restrictions, or inference guarantees distinguish this paper from those closest papers.
  - *Fix:* Add a focused paragraph or compact comparison table for the closest transported-noncompliance, two-sample weak-IV, transported-ATE minimax, and weak-LATE/MTE papers. For each, state the estimand, data structure, weak-identification treatment, transport or extrapolation assumption, and how the present \(t_n=n\mu_n^2/\kappa_n\) expected-length frontier differs.
- **[major·prose] Setup, Transport, and Honest Risk** — The assumptions are stated precisely, but their substantive content is not sufficiently interpreted. In particular, target-average receipt transport, conditional outcome-contrast transport, transport domination, the envelope \(w\le 2k_n\), \(\kappa_n\le k_n\), and \(k_n=o(n^{1/2})\) are central to the contribution yet read mainly as formal gates.
  - *Fix:* Add a short assumptions discussion after the model class that explains what each transport and dispersion condition permits in applications, how it relates to trial-to-target generalization with noncompliance, and why the finite-cell learning result uses the sub-root cell-growth regime.
- **[minor·prose] Oracle Frontier and Score Inversion** — The sentence "For weak effective strength, expected length remains bounded away from zero; once effective strength is fixed away from zero, the order improves at the inverse square-root rate in \(t_0\)" is easy to misread because the theorems fix a positive threshold \(t_0\) and study the frontier as a function of that threshold, rather than a sample-size transition within a single row sequence.
  - *Fix:* Rewrite to foreground the threshold-indexed comparison, for example: "As the threshold \(t_0\) varies, the lower bound is constant for small \(t_0\) and scales as \(t_0^{-1/2}\) at larger effective-strength thresholds."
- **[minor·prose] abstract** — The sentence "The lower bound is witnessed by a unit-transport-weight submodel" is accurate but still too compressed for readers: it does not say that this is a least-favorable submodel embedded in the transported class, which is the reason a no-shift geometry can prove a transported converse.
  - *Fix:* Revise to: "The lower bound follows from a least-favorable unit-transport-weight submodel embedded in the stated transported classes, while the attaining score-inversion bound uses \(t_n\) to combine first-stage strength and weight dispersion."
- **[minor·structure] appendix** — The proof section presents long informal proof narratives after stating that the formal results are Lean-verified. This is useful, but the relationship between the prose proof, the theorem statements, and the Lean verification scope is not completely transparent to a reader deciding what is machine checked and what is expository.
  - *Fix:* Add a brief opening paragraph to the appendix stating that the formal theorem statements and proof obligations are verified in Lean, while the displayed proof prose is a reader-facing explanation aligned to those checked declarations and external citations.

## Questions for authors
- Can the authors identify the two or three closest papers and state exactly which object in this manuscript is absent from those papers: the transported-CACE estimand, the honest expected-length frontier, the \(n\mu_n^2/\kappa_n\) scaling, or the feasible finite-cell construction?
- Are the finite-cell results intended mainly as methodological benchmarks, or as implementable procedures for common empirical designs? The answer should guide how much implementation detail and assumption interpretation appears in the main text.

