# Referee review

**Recommendation:** major_revision
**Overall score:** 6.8/10 — The verified core results are coherent and potentially useful, but the manuscript still needs substantial expository repair before the contribution is publication-ready.

The paper characterizes honest expected-length frontiers for transported complier ratios under weak transported first stages and transport-weight dispersion, with oracle, fixed-geometry, and finite-cell feasible results. The formal statements appear faithful to the verification contract, and the central rate claim is well supported. The main weaknesses are presentation and scope management: several hypotheses read as artificial artifacts of the formalization, the finite-cell contribution is buried under repeated assumption lists, and parts of the prose still create avoidable ambiguity about what is fixed, learned, or supplied by the oracle.

## Strengths
- The central contribution is clear and nontrivial: the effective-strength index n mu_n^2 / kappa_n unifies weak first stages and transport-weight dispersion for honest expected-length risk.
- The paper gives matched lower and upper bounds, plus fixed-geometry and finite-cell feasible constructions, rather than only an identification or pointwise inference result.
- The compact parameter-space treatment is a useful way to distinguish this problem from unbounded weak-ratio impossibility results.
- The formal theorem statements in the manuscript are faithful to the supplied verification contract.

## Findings
- **[major·statement] Oracle Frontier and Score Inversion** — The theorem statement for \cref{obj:thm:oracle-score-inversion-attainment} still includes an "Admissible geometry" hypothesis, and the surrounding prose says, "Read the theorem's ‘Admissible geometry’ bullet as an ambient-carrier existence condition..." This remains easy to misread as a fixed-geometry input to a theorem that is otherwise advertised as global oracle attainment.
  - *Fix:* Move the admissible-geometry existence requirement into a preliminary nonemptiness/carrier condition before the theorem, or rename the bullet to "Nonempty admissible carrier" and state explicitly inside the theorem that the displayed rule is evaluated law by law using each law's canonical weight and propensity.
- **[major·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the entire \(\mathcal P_n\) checklist immediately after defining \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\). This obscures that the finite-cell class adds one restriction to the transported model.
  - *Fix:* Replace the repeated list with a short definition that references \(\mathcal P_n\) and adds only \cref{obj:ass:finite-cell-source}; put the full inherited checklist in an appendix table if traceability is needed.
- **[major·citation] Related Literature and Discussion** — The related-work section cites very recent or apparently forthcoming work such as \citet{ChenHuang2025}, \citet{Ross2026}, and \citet{SmuclerLanniMasip2025} without giving the reader enough bibliographic or substantive orientation to evaluate priority and scope.
  - *Fix:* Add precise publication status and a one-sentence description of each directly related paper's estimand, design, and inference target; make clear which results are identification, estimation, robust inference, or minimax frontier results.
- **[minor·structure] Setup, Transport, and Honest Risk** — The discussion after \cref{obj:ass:receipt-transport} is much longer and more application-specific than the surrounding assumption explanations, mixing interpretation, validation design, and an appointment-reminder example before the risk objects are introduced.
  - *Fix:* Shorten this paragraph to the identification role of the assumption and move the validation/example material to the discussion or an examples subsection.
- **[minor·prose] appendix** — The appendix proof narratives still contain formalization-process phrasing such as "the empty branch," "discharged," and repeated references to row-zero conventions. This distracts from the econometric proof narrative.
  - *Fix:* Rewrite these passages in ordinary mathematical prose, e.g. "The finitely many initial indices are immaterial for the limiting statement" and remove implementation-flavored terms.
- **[minor·prose] global** — The manuscript uses both "least-favorable" and "least-favourable" in reader-facing text and object titles.
  - *Fix:* Standardize spelling throughout, preferably to "least-favorable" to match the theorem and definition labels already used.
- **[minor·prose] Oracle Frontier and Score Inversion** — The sentence "The selected geometry is not an input to the score rule" violates the affirmative prose contract outside a limitations section and is also a symptom of the ambiguity around the admissible-geometry hypothesis.
  - *Fix:* Rewrite affirmatively, for example: "The displayed score rule is evaluated law by law with the canonical density ratio and row-\(n\) propensity supplied by the law under evaluation."
- **[minor·structure] appendix** — The verification note says the proof narratives are "expository companions to the checked Lean declarations," but the table includes several presentation-synthesized definitions with no Lean declaration. This may lead readers to overread the verification scope.
  - *Fix:* Split the table into verified Lean declarations and presentation-synthesized notation, or add a short column/status note explaining that synthesized definitions are manuscript notation rather than checked top-level declarations.

## Questions for authors
- Can the admissible-geometry hypothesis in the global oracle-attainment theorem be reformulated as a pure nonemptiness or carrier condition so that readers do not infer a fixed-geometry oracle?
- Are the very recent cited papers final, working-paper, or forthcoming versions, and do their bibliographic entries make that status clear?

