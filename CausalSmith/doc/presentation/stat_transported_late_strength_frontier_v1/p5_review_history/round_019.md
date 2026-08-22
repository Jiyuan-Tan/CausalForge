# Referee review

**Recommendation:** major_revision
**Overall score:** 6.8/10 — The verified core delivers a coherent and potentially useful minimax frontier, but the manuscript needs stronger positioning, cleaner scope discipline, and several prose repairs before it reads like a publishable econometrics paper.

The paper characterizes honest expected-length rates for transported complier-effect confidence sets under weak transported first stages, with matched oracle, fixed-geometry, and finite-cell feasible results. The formal statements are substantial and, under the verification contract, appear faithfully represented in the main theorem displays. The current manuscript is strongest technically but weaker as an econometrics submission because the novelty is not benchmarked in enough detail against the closest weak-IV and transported-CACE papers, and several running-text passages drift into unsupported or negatively framed scope claims.

## Strengths
- The effective-strength index n mu_n^2/kappa_n is a clean organizing contribution that combines weak first stages and transport-weight dispersion.
- The paper delivers matched lower and upper expected-length rates in oracle and fixed-geometry settings, plus feasible finite-cell weight-learning procedures.
- The compact causal range is well integrated into the expected-length criterion and distinguishes the result from unbounded ratio-parameter impossibility results.
- The formal statements are explicit about assumptions, constants, procedure classes, and asymptotic regimes.

## Findings
- **[major·citation] related work** — The closest-literature comparison is too high-level for publication in a leading econometrics journal. For example, the paragraph says that Chen and Huang provide strong-first-stage transported-CACE inference, Choi/Gu/Shen and Choi/Shen address two-sample weak IV, and Ma and Smucler/Lanni/Masip provide weak-identification-robust LATE confidence sets, but it does not spell out their exact inferential targets, whether their parameter spaces are bounded, whether their length criteria are minimax, and which assumptions drive the comparison.
  - *Fix:* Add a compact comparison table or tightly written subsection listing the closest papers by estimand, sampling design, first-stage regime, transport-weight status, parameter-space geometry, guarantee, and rate/length result. Use that comparison to state exactly where this paper's oracle and finite-cell theorems sit.
- **[major·prose] cell weight learning** — The feasible contribution may read broader than the verified scope. The sentence "Together, \cref{obj:thm:finite-cell-unknown-weight-attainment,obj:thm:regular-cell-unknown-weight-attainment} show that finite-cell target-weight learning preserves the honest minimax expected-length order obtained by the oracle score inversion" does not foreground that this is proved only for the uniform finite-cell class and the known regular nonuniform-cell class with known source cell probabilities and known propensity.
  - *Fix:* Rewrite the sentence to state the exact delivered scope affirmatively: "In the uniform finite-cell class and in the known regular nonuniform-cell class with known source cell probabilities and known propensity, empirical target-cell frequencies and collision dispersion estimates attain the oracle expected-length order."
- **[major·prose] discussion and limitations** — The phrase "learning the target weights preserves the same honest minimax expected-length order as the oracle benchmark" again reads like a general feasible-weight-learning theorem, while the verified results establish this for finite-cell designs under the stated growth and known-design conditions.
  - *Fix:* Qualify the sentence with the theorem classes and inputs: uniform cells with balanced assignment, and regular nonuniform cells with known q_{x,n} and known cell-varying propensity.
- **[minor·prose] setup and assumptions** — The subsection "Reading the design restrictions" contains non-coverage prose outside the limitations section: "this is a design the experimenter can implement, not an assumption about nature" and "Relaxing any of the three moves outside what the theorems here cover."
  - *Fix:* Move genuine non-coverage content to "Limitations and future work" and rewrite the design paragraph affirmatively, e.g. "The theorem covers stratified experiments with equal source-cell masses, balanced assignment, and k_n=o(sqrt n), where the design records the cell probabilities and assignment rates."
- **[minor·prose] related work** — The sentence "the transported setting adds a covariate shift whose weight dispersion enters the rate through the Kish deflation, which has no analogue there" uses contribution-by-negation and risks overstating the comparison without a precise benchmark.
  - *Fix:* Rewrite affirmatively: "The transported setting adds a covariate-shift component, and the present frontier indexes that component through Kish dispersion." Then cite or discuss the exact Choi/Gu/Shen and Choi/Shen objects being contrasted.
- **[minor·prose] intro** — The introduction states that the lower bound is "matched by an oracle Anderson--Rubin/Fieller score inversion." The verified result supplies an Anderson--Rubin/Fieller-style transported score inversion, but the procedure is not literally a classical Fieller interval and is restricted to the compact parameter space.
  - *Fix:* Use the more precise formulation already used later: "matched by an oracle score inversion in the Anderson--Rubin and Fieller tradition, restricted to Theta=[-1,1]."
- **[minor·prose] oracle minimax rates** — The sentence "The lower bound treats Kish dispersion as part of the information scale" is plausible but informal; the formal theorem establishes rates in t_n=n mu_n^2/kappa_n rather than a separate monotone information ordering in kappa_n.
  - *Fix:* Tie the interpretation directly to the theorem: "The lower bound is expressed in the strength index t_n=n mu_n^2/kappa_n, so the same first-stage mean enters the bound through its dispersion-normalized scale."
- **[minor·structure] abstract** — The abstract is accurate but dense and theorem-list-like. It gives many conditions and classes in one paragraph, which makes the contribution hard to parse for readers before the notation is introduced.
  - *Fix:* Split the abstract into two short paragraphs: one for the estimand/design and effective-strength scale, one for the oracle and feasible finite-cell results with their exact classes.
- **[minor·prose] setup and assumptions** — The first-use gloss rule is mostly satisfied, but several early symbols appear with only mathematical definitions and little plain-word anchoring, notably k_n in the weight envelope and kappa_n in the main rate discussion.
  - *Fix:* At first use, attach short appositives such as "k_n, the cell/envelope scale" and "kappa_n, the second moment of the transport weights."
- **[nit·prose] appendix** — The appendix proof text contains small typography inconsistency: "least-favourable" appears alongside the paper's predominantly American spelling "least-favorable."
  - *Fix:* Standardize the spelling throughout the manuscript.

## Questions for authors
- Can the related-work section state whether any closest weak-IV or transported-CACE benchmark gives an expected-length minimax rate under a bounded causal parameter space?
- Are the finite-cell procedures intended as implementable recommendations for stratified experiments, or as proof-of-concept feasibility results for target-weight learning under controlled discrete designs?
- Will the final version include a short formalization-scope note or footnote at the theorem-local level, as indicated by the verification contract?

