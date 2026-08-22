# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The verified core results are interesting and plausibly publishable, but the manuscript still needs substantial expository repair around result typing, contribution scope, and finite-cell assumptions before it reads like a journal submission.

The paper establishes an honest minimax expected-length frontier for transported complier ratios under weak transported first stages and transport-weight dispersion, with oracle and finite-cell feasible attainability results. The verified statements support the central rate claim, and the contribution is meaningful for researchers working on transported noncompliance and weak-IV robust inference. The current manuscript is mathematically credible but too checklist-heavy, and several prose choices blur notation, assumptions, and proved claims.

## Strengths
- The central frontier indexed by \(n\mu_n^2/\kappa_n\) is a clean and useful synthesis of weak first stages and covariate-shift dispersion.
- The paper gives both lower and upper oracle results and connects them to feasible finite-cell target-weight learning.
- The main theorem prose is largely faithful to the verification contract and states the relevant overlap, envelope, sample-size, and growth conditions.
- The paper positions the work at a meaningful intersection of LATE, weak-IV robust inference, and transportability.

## Findings
- **[major·structure] Fixed Geometry and Feasible Cell Weight Learning / Appendix** — The object titled "Geometry handle \(Q_{n,h}^{\mathfrak g}\)" is presented as a definition but contains substantive chi-square and total-variation inequalities: "the corresponding least-favorable laws satisfy..." This reads as a proved separation result, not merely notation.
  - *Fix:* Retype this environment as a lemma/proposition, or split it into a short definition of the notation and a separate lemma stating the chi-square and total-variation bounds.
- **[major·structure] Setup, Transport, and Honest Risk / Appendix** — The finite-cell class is introduced twice: first as the simple nesting \(\mathcal N_n=\{P\in\mathcal P_n:P\text{ satisfies }\cref{obj:ass:finite-cell-source}\}\), and later as a full repeated checklist of all assumptions. This repetition obscures the submodel relation that is important for the oracle-to-feasible comparison.
  - *Fix:* Keep the main text definition as the nesting relation and move the full checklist to a compact appendix note only if needed for formal traceability; otherwise replace the checklist with one sentence saying that \(\mathcal N_n\) inherits all conditions defining \(\mathcal P_n\) and adds \cref{obj:ass:finite-cell-source}.
- **[minor·prose] Oracle Frontier and Score Inversion** — The "Nonempty admissible carrier" bullet in \cref{obj:thm:oracle-score-inversion-attainment} can still be read as making the oracle score procedure conditional on one fixed geometry, although the theorem's procedure is evaluated law by law using each law's canonical transport weight and propensity.
  - *Fix:* Rename the bullet to "Nonempty admissible model domain" and add a sentence immediately after the theorem statement saying that this hypothesis supplies a nonempty comparison class, while the score-inversion rule itself uses the evaluated law's own canonical \(w\) and \(e\).
- **[minor·citation] Related Literature and Discussion** — The nearest recent comparators remain bibliographically hard to assess from the manuscript excerpt, especially Chen--Huang, Ross et al., Ma, and Smucler--Lanni--Masip. These papers define the closest novelty boundary for transported CACE and weak-identification-robust LATE inference.
  - *Fix:* Ensure the bibliography gives full, searchable citation information for these works, including titles, venue or arXiv identifiers, and dates; in the related-work paragraphs, identify the precise inferential target each comparator treats and the positive scope added by this paper.
- **[minor·prose] Setup, Transport, and Honest Risk** — Some assumption commentary still uses conventionality language for specialized restrictions, for example "Outcome-contrast transport is the standard conditional transport..." and nearby discussion of receipt transport. The receipt condition is an integrated target-law equality rather than the usual covariate-conditional transport condition.
  - *Fix:* Revise the assumption commentary to distinguish standard IV ingredients from the paper-specific transported-IV restriction: describe receipt transport affirmatively as the integrated target-law denominator link used here, and reserve "standard" for genuinely conventional overlap, randomization, exclusion, and monotonicity conditions.
- **[minor·prose] Appendix: Proofs, Auxiliary Arguments, and Verification Note** — The appendix remains quite long and procedural, with proof steps often written as formal bookkeeping rather than econometric argument. The verification note is now concise, but the proof narratives still lean heavily on phrases such as "changing finitely many initial indices," "boundedness hypotheses for passing the eventual inequality through limsup," and repeated class-nonemptiness bookkeeping.
  - *Fix:* Condense repeated measure-theoretic and limsup bookkeeping into reusable lemmas or a preliminary paragraph, and make each proof foreground the statistical mechanism: identification, least-favorable perturbation, score-inversion coverage, and finite-cell weight learning.
- **[nit·prose] global** — The manuscript generally follows the cleveref contract, but there are a few prose phrases that manually name an object immediately before a reference, such as "the compact range result in \cref{obj:prop:compact-causal-range}" and "the fixed-geometry value from \cref{obj:def:fixed-geometry-value}." This is less severe than using \ref, but it partly defeats the target-environment naming discipline.
  - *Fix:* Use direct cleveref phrasing where possible, for example "\Cref{obj:prop:compact-causal-range} gives..." and "\cref{obj:def:fixed-geometry-value} defines...".

## Questions for authors
- Can the finite-cell and regular-cell feasible procedures be illustrated with a small numerical example or schematic table showing the empirical target frequencies, cellwise source contrasts, and collision statistic?
- Are the constants intended as practically usable critical values, or only as proof constants for rate attainability?

