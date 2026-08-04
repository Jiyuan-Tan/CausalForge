# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The verified results deliver a meaningful minimax frontier, but the manuscript still needs substantial expository and positioning revision before it reads as a publishable econometrics article.

The paper studies honest expected length for transported complier-effect ratios under weak transported first stages and dispersed transport weights. The verified core contribution is a matched oracle and finite-cell minimax order, indexed by n mu_n^2 / kappa_n, with Anderson--Rubin style score inversion attaining the frontier. I find the main claims largely faithful to the verified theorem statements, but the manuscript remains too formalization-forward, repetitive in its assumption architecture, and under-oriented relative to the closest recent literature.

## Strengths
- The central effective-strength index n mu_n^2 / kappa_n is clear, economically interpretable, and useful for connecting weak-IV and transport-weight dispersion.
- The oracle lower and upper bounds, fixed-geometry result, and finite-cell feasible attainability form a coherent theoretical package.
- The manuscript is careful about compact parameter geometry and avoids the classical unbounded-ratio impossibility framing as a substitute for its positive result.
- The main theorem statements track the verification contract closely and generally avoid overselling the formal scope.

## Findings
- **[major·citation] Related Literature and Discussion** — The related-work section cites very recent or apparently forthcoming work such as \citet{ChenHuang2025}, \citet{Ross2026}, and \citet{SmuclerLanniMasip2025} without enough bibliographic or substantive orientation for readers to assess priority, overlap, and whether the present paper's frontier result is the first of its kind in the transported-CACE setting.
  - *Fix:* Add 1-2 precise sentences for each closest recent paper stating its object, design, inferential target, and how the present minimax expected-length characterization differs under the stated compact transported-ratio and finite-cell conditions.
- **[minor·prose] Oracle Frontier and Score Inversion** — The theorem statement for \cref{obj:thm:oracle-score-inversion-attainment} still includes an "Admissible geometry" bullet, and the prose says, "Read the theorem's ‘Admissible geometry’ bullet as an ambient-carrier existence condition..." This remains easy to misread as making the global oracle score rule conditional on a fixed geometry.
  - *Fix:* Move the admissible-geometry clause into a short nonemptiness or carrier-existence sentence before the theorem, or rename the bullet to "Nonempty admissible carrier" and state affirmatively that the displayed score rule is evaluated law by law with the law's canonical weight and propensity.
- **[minor·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the entire \(\mathcal P_n\) checklist immediately after the text defines \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\). This obscures the simple relationship between the full transported model and the finite-cell submodel.
  - *Fix:* Replace the repeated checklist in the reader-facing definition with the one-line submodel definition plus a sentence that the formal checklist is recorded for verification traceability; if the checklist is retained, put it in an appendix table rather than the main setup.
- **[minor·prose] appendix** — The appendix proof narratives still use formalization-process language, including phrases such as "The single initial index is covered," "empty frontier rows," "empty/nonempty split," and repeated row-zero conventions. This makes the proof section read like an implementation log rather than an econometric argument.
  - *Fix:* Rewrite these passages in conventional asymptotic prose, e.g. "finite initial rows do not affect the limiting coverage or risk" and "when the strength-restricted class is empty, the supremum convention is immaterial to the limiting bound."
- **[minor·prose] Setup, Transport, and Honest Risk** — The discussion after \cref{obj:ass:receipt-transport} is longer and more interpretive than the surrounding assumption explanations, especially the sentence beginning "It identifies the transported Wald denominator..." before the risk objects have been introduced.
  - *Fix:* Shorten the post-assumption explanation to the role of the condition in identifying the transported first stage, and move discussion of target covariate sample use to the feasible-procedure section.
- **[nit·prose] appendix** — The verification note says, "Presentation-synthesized notation, such as the score radius and fixed-geometry distance notation, is manuscript notation used to state the checked results," but the checked-status table itself lists only theorem results. The status boundary is mostly clear, but the surrounding wording could still be read too broadly.
  - *Fix:* State explicitly that presentation-synthesized definitions are notation-management devices and are outside the top-level Lean theorem checklist unless separately named by a checked declaration in the verification contract.

## Questions for authors
- Which of Chen and Huang, Ross et al., Ma, and Smucler--Lanni--Masip are published, forthcoming, or working papers, and what exact overlap do they have with minimax expected length rather than confidence-set construction or identification?
- Can the main text state the finite-cell model as a one-restriction submodel of \(\mathcal P_n\) and reserve the verification checklist for the appendix?
- Is the intended audience expected to read the Lean verification note as part of the paper's methodological contribution, or only as an audit trail for the theorem statements?
