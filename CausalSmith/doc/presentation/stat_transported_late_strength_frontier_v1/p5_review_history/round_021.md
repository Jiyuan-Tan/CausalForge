# Referee review

**Recommendation:** major_revision
**Overall score:** 7/10 — The paper delivers a useful and formally verified minimax frontier, but several prose and presentation choices overstate feasibility/scope or obscure the exact conditioning and design restrictions.

The submission characterizes honest expected-length rates for transported complier-ratio confidence sets under weak first stages, with oracle, fixed-geometry, finite-cell, and known regular-cell results. The verified formal layer supports the main mathematical contribution, and the topic is relevant to weak-IV and transportability audiences. Publication requires revision to align the prose with the exact theorem scope, sharpen positioning, and reduce the burden imposed by excessive formal machinery in the main text.

## Strengths
- The effective-strength index n mu_n^2 / kappa_n is a clear and useful synthesis of weak first stages and transport-weight dispersion.
- The paper provides matched lower and upper expected-length rates, including fixed-geometry and feasible finite-cell versions.
- The formal statements are precise and the verification contract supports the mathematical claims made in the theorem environments.
- The related-work section identifies the closest transported-CACE and weak-IV literatures rather than relying only on broad citations.

## Findings
- **[major·prose] setup and assumptions** — The sentence "Relaxing any of the three moves outside what the theorems here cover" violates the affirmative contribution framing rule outside a limitations/future-work section and frames the design discussion by non-coverage.
  - *Fix:* Rewrite affirmatively in that section, e.g. "The theorems cover designs with known strata, supplied assignment probabilities, and k_n=o(sqrt n), the regime in which the cell-frequency and collision terms are calibrated at the oracle rate." Move any genuine non-coverage discussion to the Limitations and future work subsection.
- **[major·prose] abstract** — The abstract states the finite-cell results as "empirical target cell frequencies yield a score inversion that uses the samples alone to supply the target weights" before clearly separating the uniform sample-only case from the regular-cell case that uses known source cell probabilities and known propensity.
  - *Fix:* Revise the abstract to state the exact information sets in one sentence: the uniform class is sample-only with balanced assignment, while the regular nonuniform extension uses the samples plus known source cell probabilities and known cell-varying propensity.
- **[major·prose] intro** — The sentence "The oracle class in \cref{obj:def:oracle-honesty} allows the procedure to use the target-to-source density ratio and the source assignment propensity" is accurate, but the following prose presents the oracle score inversion as the central constructive procedure without enough early separation from feasible implementability in the general transported model.
  - *Fix:* Add an explicit affirmative scope sentence near the first oracle discussion: "This construction is an oracle benchmark for the general model; feasible target-weight learning is established in the finite-cell classes stated in \cref{obj:thm:finite-cell-unknown-weight-attainment,obj:thm:regular-cell-unknown-weight-attainment}."
- **[major·statement] oracle minimax rates** — The theorem title "Oracle score inversion" and surrounding sentence "The matching upper bound is attained by the oracle score-inversion rule" may be read as a general feasible construction, while the verified theorem requires oracle-known w and e plus an admissible geometry existence condition.
  - *Fix:* Rename or qualify the theorem-facing prose, e.g. "Oracle-known-weight score inversion," and state immediately before the theorem that the procedure uses the true density-ratio version and propensity as oracle inputs.
- **[major·citation] related work** — The closest-results subsection is useful but still too qualitative for several comparisons; for example, the Ma and Smucler-Lanni-Masip paragraph says those papers "deliver coverage guarantees" while this paper contributes a "matching expected-length frontier," but it does not state whether their parameter spaces, expected-length criteria, or compact-range assumptions make the comparison directly comparable.
  - *Fix:* Add a compact comparison table or two additional sentences per closest paper giving the exact guarantee type, parameter geometry, and whether expected length is studied. This is literature positioning work, not a new theorem.
- **[minor·prose] discussion and limitations** — The sentence "Their matched lower and upper bounds show that, in the stated finite-cell designs, in the uniform finite-cell class with balanced assignment, and in the regular nonuniform-cell class with known cell probabilities and known cell-varying propensity, learning the target weights attains the same honest minimax expected-length order as the oracle benchmark" is repetitive and syntactically confusing.
  - *Fix:* Rewrite as one scoped claim: "In the uniform finite-cell class with balanced assignment and in the regular nonuniform-cell class with known source cell probabilities and known cell-varying propensity, the feasible procedures attain the oracle expected-length order."
- **[minor·structure] global** — Several formal statements include long lists of assumptions already implied by class membership, which makes it hard for readers to see which restrictions are substantive for each result.
  - *Fix:* Add a short assumption map or table before the theorem section listing the classes, information available to procedures, and extra row conditions for each theorem; keep the verified statements intact.
- **[minor·structure] proofs, auxiliary arguments, and verification note** — The appendix proof section is extremely long and mixes reader-facing proof intuition, formal-audit scaffolding, and verification metadata. This reduces readability for econometrics readers.
  - *Fix:* Move routine inhabitation and measurability lemmas into a separate technical appendix subsection, and start the proof appendix with a dependency graph showing which auxiliary lemmas support each main theorem.
- **[minor·prose] verification note** — The verification note states "The note covers the local mathematical claims..." but does not clearly distinguish Lean-verified results from cited external scholarly context in the page-facing text.
  - *Fix:* Add one concise sentence distinguishing verified formal reductions from bibliographic positioning, and ensure any theorem-local formalization-scope footnote required by the project appears at cited external-dependency uses.
- **[nit·prose] global** — The notation alternates between \(P_T\), \(P_{T,n}\), \(P_S^X\), and \(P_{S,n}^X\), and between \(H_i\) and \(H(O^S)\), sometimes before reminding the reader of the array index.
  - *Fix:* Add a notation paragraph after the setup opening that states when the index n is suppressed and standardizes the source-score notation.

## Questions for authors
- Can the closest-results subsection state explicitly whether the existing weak-LATE papers study expected length under compact parameter spaces, so the novelty claim is auditable without inference?
- Do the authors intend the oracle score inversion to be viewed only as a benchmark for the general transported model, with feasibility currently established only in the finite-cell classes?
- Would a table of theorem classes, information sets, and rates be acceptable, given the number of model classes and procedure classes introduced?

