# Referee review

**Recommendation:** reject
**Overall score:** 4.2/10 — The verified mathematics appears coherent and exact, but the submission is too narrow and too weakly connected to econometric design or inference to earn publication in a leading econometrics journal as written.

The paper gives an exact finite-dimensional characterization of implementability loss for a highly symmetric two-block covariance-design problem, with several sharp Lean-verified results. The core mathematical note is careful and potentially useful to readers interested in SDP/correlation-polytope geometry for experimental design. However, the econometric contribution is substantially oversold: the objective is assumed rather than derived from an estimand, estimator, risk, or welfare criterion, and several prose claims draw broader design-practice implications than the formal results support.

## Strengths
- The formal statements are precise, finite-sample, and apparently faithfully represented by the verification contract.
- The symmetry reduction and parity-truncation characterization give a clean explanation of when the relaxation is exactly implementable in this stylized slice.
- The paper is unusually transparent about the boundary between verified mathematics and interpretation.
- The worked example helps make the abstract geometry more concrete.

## Findings
- **[major·prose] global** — The contribution is too narrow for the econometrics framing as written. The paper explicitly says, "we take the objective F_{r,\kappa} as given---a covariance design criterion ... and do not derive it from a specific estimand, estimator, variance, or welfare target," but the title, introduction, and discussion frame the work as a contribution to randomized experiments under interference.
  - *Fix:* Either add a substantive econometric result deriving F_{r,\kappa} and the loss from a stated estimand/estimator/risk problem, or retitle and reposition the paper as a mathematical note on implementability of a particular covariance criterion rather than as an econometrics design paper.
- **[major·prose] abstract** — The abstract presents the norm term as a "Schatten--2 robustness penalty" and says iid assignment is an "asymptotic target as the robustness weight diverges." The verified layer proves facts about a Schatten--2 norm penalty; it does not establish statistical robustness, minimax robustness, robustness to graph misspecification, or robustness of inference.
  - *Fix:* Replace "robustness" language with neutral terminology such as "Schatten--2 norm penalty" unless a formal robustness interpretation is added. If the term is retained, state exactly what kind of robustness is meant and what is not claimed.
- **[major·prose] discussion** — The paper repeatedly draws design-practice implications that exceed the formal scope. For example, "For interference-aware randomized design, the practical implication is that solving the covariance relaxation is not by itself enough" is true only for this two-block, sign-symmetric, block-exchangeable, no-fixed-count criterion, not for interference-aware randomized design generally.
  - *Fix:* Qualify all design-practice implications with the maintained model and criterion, or add results showing the same phenomenon in broader design classes, objectives, or networks.
- **[major·citation] positioning** — The novelty claim around the parity-truncated characterization is under-supported. The discussion says, "We are not aware of a prior statement of this parity-truncated characterization..." but the paper does not engage enough with finite exchangeability, Rademacher moment problems, or low-dimensional correlation-polytope slices to substantiate novelty at journal standard.
  - *Fix:* Add a focused related-work discussion on exchangeable Rademacher moment sets, correlation-polytope projections, and two-block or exchangeable slices, and state precisely whether the parity truncation is new or a specialization of known moment-characterization results.
- **[major·other] verification note** — The verification note lists Lean version, mathlib revision, namespace, and declaration names, but it does not provide an accessible artifact, build command, or archival identifier. For a paper relying on machine checking, this is insufficient reproducibility information.
  - *Fix:* Provide a repository or archive link, exact commit, build instructions, dependency setup, and the command that checks the relevant declarations.
- **[minor·statement] positive loss and sharp computation** — The theorem title "Sharp Rounding Loss" is misleading because no rounding algorithm is defined or analyzed. The theorem computes an implementability or truncation loss, not the loss of a specified rounding procedure.
  - *Fix:* Rename the theorem and all surrounding references to "Sharp Implementability Loss" or "Sharp Truncation Loss" unless an actual rounding procedure and guarantee are introduced.
- **[minor·prose] positive loss and sharp computation** — The worked example and Table 1 risk implying a comprehensive phase diagram. The table heading "Regime" can be read as partitioning the parameter space, even though the cut and gap results leave intervals not classified by the named theorems and the paper explicitly disclaims global boundaries.
  - *Fix:* Rename the table to "Selected Certified Cases" or similar, add an explicit row for unclassified regions, and state that only the active-set formula is global.
- **[minor·prose] intro** — The sentence "no generality is lost in the benchmark" is easy to overread, even though the next paragraph narrows the claim. The reduction is only for the specific invariant objective and sign-symmetric feasible class.
  - *Fix:* Revise the sentence to say "no generality is lost for optimizing this invariant objective over the maintained sign-symmetric class" and avoid broader benchmark language.
- **[minor·structure] setup and assumptions** — The label "Balanced Sign Symmetry" and notation \(\mathcal P_m^{\mathrm{bal}}\) invite confusion because the condition does not impose fixed treated counts or exact realized balance.
  - *Fix:* Rename the condition and class to something like "Global Sign Symmetry" and \(\mathcal P_m^{\mathrm{sgn}}\), or repeatedly use the full phrase "sign-symmetric, not fixed-count" in headings and theorem statements.
- **[minor·prose] setup and assumptions** — The scale convention \(W_{ij}=a/m,b/m\) and the low-scale condition \(a+3b<2m\) are stated but not economically motivated. A reader is left unsure whether \(a,b\) are fixed intensities, growing with \(m\), or normalized degrees.
  - *Fix:* Add a short paragraph explaining the normalization, the intended asymptotic or finite-sample scaling of \(a,b\), and how the low-scale condition should be interpreted in graph-weight terms.
- **[minor·structure] positive loss and sharp computation** — The paragraph introducing the active-set ingredients says these objects are "established in Appendix~\ref{sec:deferred-proofs} (Lemmas...)" but the lemmas themselves are collected in Appendix A, while \(\ref{sec:deferred-proofs}\) labels the later proof-sketch appendix.
  - *Fix:* Correct the cross-reference to Appendix A or split the labels so that the lemma collection and proof sketches are separately referenced.
- **[minor·prose] abstract** — The abstract is too dense and uses theorem-local phrases before notation is introduced, such as "the stated low-scale condition" and "the stated robustness range." This makes the contribution hard to parse for readers not already inside the formal development.
  - *Fix:* Rewrite the abstract around the question, setting, main qualitative results, and limitations; move detailed inequalities and theorem-specific qualifiers to the introduction.
- **[nit·prose] positive loss and sharp computation** — Notation alternates between \(z_{\mathrm{sp}}\), \(z\), and explanations about an "ambient sign index." The truncation lemma also uses \(z\) where the main text uses \(z_{\mathrm{sp}}\).
  - *Fix:* Use one notation consistently for the aggregate spectral coordinate, preferably \(z_{\mathrm{sp}}\), and reserve plain \(z\) for realized assignment vectors only.

## Questions for authors
- What econometric estimand, estimator, or loss function is F_{r,\kappa} intended to approximate or upper-bound in the target applications?
- Is the parity-truncated two-block Rademacher moment characterization genuinely new relative to known finite-exchangeability or correlation-polytope projection results?
- Can the active-set formula be packaged as reproducible code so readers can compute \(\Delta_m^{\pm}\) for parameter values beyond the worked example?

