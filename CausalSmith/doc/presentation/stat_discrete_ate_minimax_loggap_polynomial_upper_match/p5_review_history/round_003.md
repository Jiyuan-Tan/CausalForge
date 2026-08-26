# Referee review

**Recommendation:** minor_revision
**Overall score:** 8.2/10 — The paper delivers a technically meaningful and well-scoped minimax contribution with unusually good claim fidelity, but it still needs presentational and reproducibility tightening before publication.

The submission studies ATE estimation with unrestricted finite-alphabet confounding and establishes the fixed-interior minimax rate n^{-1}+d^2/(n^2 log^2 n), with a constructive hybrid estimator and a separate exact-randomization endpoint result. The verified statements support the main contribution, and the prose is generally careful about the calibrated range, fixed-overlap constants, and the non-adaptive nature of the near-randomization selector. I would recommend publication after minor revision, mainly to make the human-readable exposition and reproducibility layer match the strength of the formal result.

## Strengths
- The main rate result is novel and important for researchers studying uniform causal inference with high-dimensional or sparse discrete covariates.
- The paper is unusually disciplined about scope: the fixed-interior range, dependence on epsilon, imported lower-bound ingredient, endpoint behavior, and lack of triangular-array transition theory are mostly stated honestly.
- The estimator is constructive rather than existential, and the heavy/light split gives a clear statistical explanation for the logarithmic improvement.
- The relationship to semiparametric, doubly robust, higher-order influence-function, and large-alphabet functional-estimation literatures is broadly accurate and useful.

## Findings
- **[minor·structure] appendix** — Several appendix proofs remain too compressed for a journal article, even though the verified statements should be treated as true. For example, the proof of Lemma 1 states that the centered term, false-light term, Chebyshev approximation bound, and calibration algebra give the desired bounds, but the reader is not shown the intermediate inequalities or where the key constants enter.
  - *Fix:* Expand the proofs of the light-cell and heavy-cell lemmas into readable mathematical derivations, or insert explicitly numbered auxiliary inequalities with short explanations before invoking them. The Lean verification can remain the certification layer, but the appendix should let a statistically trained reader follow the proof architecture without reconstructing hidden sublemmas.
- **[minor·statement] setup and assumptions** — The ATE display uses conditional means in categories where they may not be defined: "\(\tau(P)=\sum_{k=1}^{d}p_k(\mu_{1k}-\mu_{0k})=\sum_{k=1}^{d}\phi(q_k)\)." Earlier, \(\mu_{ak}\) is defined only when the conditioning event has positive probability, so the first sum is formally ambiguous for zero-mass categories.
  - *Fix:* State a convention that \(p_k(\mu_{1k}-\mu_{0k})\) is interpreted as zero when \(p_k=0\), or write the first sum over \(k:p_k>0\) and define the functional primarily by the four-cell expression \(\sum_k\phi(q_k)\).
- **[minor·prose] abstract** — The sentence "The result implies a parametric-rate window \(d=O(\sqrt n\log n)\), within the fixed-interior range, and a consistency threshold \(d=o(n\log n)\)" could still be read as a global consistency characterization, although the theorem only characterizes consistency under the calibrated fixed-interior range or in sequences eventually entering it.
  - *Fix:* Revise to say, for example, "within the calibrated fixed-interior range, this gives a parametric-rate window ... and a consistency threshold ..." so both consequences inherit the same range restriction.
- **[minor·other] verification note** — The manuscript says that the formal statements and derivations are supported by a Lean 4 development, but the submitted text does not give a precise artifact location, commit, build command, or dependency information. Since the paper relies on formal verification as part of its rigor, this is a reproducibility gap.
  - *Fix:* Add a code and verification availability paragraph with repository/DOI, commit hash, Lean/toolchain version, build instructions, and a short description of how theorem names in the manuscript map to the formal declarations.
- **[nit·prose] main results** — The title and label of the second main theorem use language such as "Universal Hybrid Envelope" and the internal label suggests overlap-adaptivity, while the selected estimator is explicitly oracle-calibrated and depends on \(\epsilon\) and \(C_\epsilon\). The surrounding prose mostly clarifies this, but the naming still risks suggesting data-driven adaptivity.
  - *Fix:* Rename the theorem or add a parenthetical sentence immediately before it such as "Universal here refers to the fixed formula of the hybrid estimator, not to data-driven adaptation to unknown overlap constants."

## Questions for authors
- Will the Lean development be submitted as a permanent, citable artifact with exact build instructions?
- Can the authors add a short comparison, even qualitative, explaining how the hybrid estimator differs operationally from the standard estimators analyzed in Zeng et al. beyond the rate statement?

