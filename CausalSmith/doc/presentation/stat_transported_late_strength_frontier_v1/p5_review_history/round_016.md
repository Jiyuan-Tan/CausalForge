# Referee review

**Recommendation:** major_revision
**Overall score:** 7.1/10 — The verified results deliver a meaningful minimax frontier, but the manuscript still needs substantial expository repair before it reads like a polished econometrics submission.

The paper studies honest expected length for transported complier-effect ratios under weak transported first stages and transport-weight dispersion, proving matched oracle lower and upper bounds and finite-cell feasible attainability. The core contribution is significant and, under the verification contract, the theorem statements are faithful to the formal layer. The main obstacles are presentation: several formal artifacts are exposed in ways that obscure the econometric logic, some assumption lists are unnecessarily repetitive, and the appendix still reads too much like a proof-audit transcript rather than a journal appendix.

## Strengths
- The effective-strength index n mu_n^2/kappa_n is a clean and useful summary of weak compliance and transport dispersion.
- The oracle converse and score-inversion attainment give a coherent matched minimax expected-length result on a compact causal range.
- The finite-cell and regular-cell results add a valuable feasible-weight-learning component rather than stopping at an oracle benchmark.
- The prose generally respects the verified theorem conditions and avoids overselling beyond the formal statements.

## Findings
- **[major·structure] Appendix: Proofs, Auxiliary Arguments, and Verification Note** — The appendix contains long proof narratives that repeatedly describe formal verification mechanics rather than the econometric argument, for example the verification table discussion and phrases such as "presentation-synthesized definitions acquire checked status when separately named by a checked declaration in the verification contract." This material weakens the paper's readability as a journal submission even though the theorem claims are verified.
  - *Fix:* Move the verification-scope material into a short standalone verification note or footnote, and rewrite the appendix proofs as mathematical arguments centered on identification, score inversion, Le Cam lower bounds, and finite-cell variance control. Keep the Lean declaration table only if the target venue explicitly welcomes formal-artifact metadata.
- **[major·structure] Fixed Geometry and Feasible Cell Weight Learning** — The object titled "Geometry handle Q_{n,h}^{\mathfrak g}" is presented as a definition but contains substantive chi-square and total-variation inequalities: "the corresponding least-favorable laws satisfy..." This is a proved separation claim, not notation.
  - *Fix:* Retitle and recast this environment as a lemma or proposition, e.g. "Least-favorable separation bound," and reserve the definition environment for the construction of Q_{n,h}^{\mathfrak g} and the distance notation.
- **[major·structure] Setup, Transport, and Honest Risk** — The finite-cell class definition repeats the full \mathcal P_n assumption checklist immediately after the text already defines \mathcal N_n={P\in\mathcal P_n:P satisfies \cref{obj:ass:finite-cell-source}}. This obscures the simple nesting relationship and burdens the reader with duplicated assumptions.
  - *Fix:* State \mathcal N_n as \mathcal P_n plus \cref{obj:ass:finite-cell-source}; replace the repeated checklist with a one-sentence inheritance statement. If a formal checklist is needed for verification, move it to the appendix or a compact display.
- **[minor·prose] Oracle Frontier and Score Inversion** — The "Nonempty admissible carrier" bullet in \cref{obj:thm:oracle-score-inversion-attainment} can still make readers think the global oracle score rule is conditional on a fixed geometry, even though the procedure is evaluated law by law with each law's canonical weight and propensity.
  - *Fix:* Rename the bullet to something like "Ambient nonemptiness" and explain in the theorem preamble that the geometry assumption supplies a nonempty comparison domain, while the score rule itself is global and uses the oracle inputs supplied by the evaluated law.
- **[minor·structure] Fixed Geometry and Feasible Cell Weight Learning / Appendix** — The no-shift result is stated before the general fixed-geometry theorem but its proof invokes \cref{obj:thm:fixed-geometry-frontier}. This makes the logical dependency harder to follow.
  - *Fix:* Either move \cref{obj:prop:no-shift-reduction} after \cref{obj:thm:fixed-geometry-frontier} in the main text, or explicitly present it as a corollary/specialization of the fixed-geometry theorem and order the appendix proofs accordingly.
- **[minor·citation] Related Literature and Discussion** — The close recent references are named but not yet bibliographically unambiguous in the manuscript excerpt, especially Chen--Huang, Ross et al., and Smucler--Lanni--Masip. Because these papers define the nearest comparison class, readers need enough bibliographic detail to locate them and assess novelty.
  - *Fix:* Audit the bibliography entries for these close references, add arXiv identifiers, journal details, titles, and dates where available, and align the text with the final bibliographic status.
- **[minor·prose] Setup, Transport, and Honest Risk** — The paper repeatedly labels assumptions as "standard" while also using specialized variants, for example receipt transport is imposed only after averaging over the target law. The prose does note this distinction, but the surrounding wording can make the assumptions sound more conventional than they are.
  - *Fix:* For the transport assumptions, add a short paragraph explaining which parts are standard support/contrast transport conditions and which parts are tailored to the transported-ratio frontier.
- **[nit·prose] global** — The manuscript contains many Lean-oriented inline symbols and references, such as \leanref{S-1}{...} and \leanref{sym:k_n}{...}. These may be useful for artifact traceability but interrupt the reader-facing exposition.
  - *Fix:* Move most \leanref material to footnotes, margin notes, or an artifact appendix, leaving the main text in conventional econometric notation.

## Questions for authors
- Is the intended journal audience expected to read the Lean verification metadata in the main appendix, or should that material be separated from the econometric proof narrative?
- Do the finite-cell feasible procedures assume the cell partition is known to the analyst in all applications, and should that be stated earlier when the feasible contribution is introduced?
