# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results deliver a clear minimax frontier and feasible finite-cell construction, with remaining weaknesses mainly in exposition, scope calibration, and literature positioning rather than theorem fidelity.

The paper studies honest confidence sets for transported complier effects in two-sample encouragement designs and characterizes the expected-length frontier through the effective strength n mu_n^2/kappa_n. The core formal claims are faithful to the verification contract and the manuscript now states the main conditions with unusual care. I would support publication after minor revision focused on making the assumptions, feasible-procedure scope, and related-work distinctions easier for econometric readers to audit.

## Strengths
- The central effective-strength index n mu_n^2/kappa_n is conceptually useful and connects weak first stages with transport-weight dispersion in a single risk scale.
- The oracle lower and upper bounds, fixed-geometry version, and finite-cell feasible procedures form a coherent matched frontier story.
- The abstract and introduction mostly preserve the exact theorem gates: overlap, bounded outcomes, compact parameter space, degrading arrays, and cell-growth conditions are visible where the contribution is stated.
- The manuscript gives unusually explicit formal definitions of honesty, risk, geometry, and finite-cell feasibility, which helps separate statistical target, oracle benchmark, and feasible procedures.

## Findings
- **[minor·prose] Setup, Transport, and Honest Risk** — The practical content of receipt-contrast transport remains somewhat underdeveloped. The paragraph after the assumption gives an example and diagnostic, but the reader is still left to infer how strong the target-average equality is relative to standard source-only LATE designs and what sampling object identifies the target compliance average in the stated two-sample setup.
  - *Fix:* Add one compact paragraph immediately after \cref{obj:ass:receipt-transport} stating affirmatively that the model is suited to applications where target-side receipt/adherence information identifies the target-law average compliance margin, and distinguish the observed target covariate sample used in the theorems from any auxiliary target receipt evidence used to support the assumption.
- **[minor·statement] Fixed Geometry and Feasible Cell Weight Learning** — The theorem title "Finite-cell weight attainment" understates the result and can be misread as only estimating weights, while the verified theorem establishes sample-only score-inversion attainment using target empirical frequencies and a collision-scale dispersion proxy.
  - *Fix:* Retitle \cref{obj:thm:finite-cell-unknown-weight-attainment} to something like "Feasible finite-cell score-inversion attainment" and adjust the first sentence after the theorem to emphasize the full confidence-set construction, not just weight learning.
- **[minor·structure] Related Literature and Discussion** — The closest-literature paragraph is clearer than before but still compresses several distinct comparisons into one long block: Chen and Huang on transported CACE, Rudolph/van der Laan and Ross on transported encouragement or adherence, Ma and Smucler et al. on weak-ID LATE, and Choi et al. on two-sample IV. This makes the novelty claim harder to parse.
  - *Fix:* Split the paragraph into two shorter paragraphs: one for transported noncompliance targets and one for weak-identification/two-sample IV inference. End each paragraph with a one-sentence affirmative statement of the paper's added frontier result under its stated conditions.
- **[nit·prose] appendix** — The appendix says "The theorem statements and proofs in this appendix are machine-checked in Lean 4," while the table only records top-level declarations and the surrounding prose also functions as an expository proof narrative. This could make readers think every explanatory sentence in the appendix is itself a formal object.
  - *Fix:* Revise the verification note to say that the top-level theorem statements and proof obligations corresponding to the listed declarations are machine-checked, while the surrounding proof narratives are expository companions to the formal artifact.
- **[nit·structure] Setup, Transport, and Honest Risk** — The finite-cell definitions repeatedly restate all assumptions already inherited from \mathcal P_n. This is faithful, but it slows the reader and obscures the single additional finite-cell restriction.
  - *Fix:* After the first full list, replace later repeated assumption lists with a shorter sentence such as "\mathcal N_n is the subclass of \mathcal P_n additionally satisfying \cref{obj:ass:finite-cell-source}" unless the paper's generation format requires the expanded checklist.

## Questions for authors
- In applications, is the target compliance-margin evidence assumed to come from the same target covariate sample, from linked administrative receipt data, or from an auxiliary validation sample? The current theoretical two-sample experiment uses target covariates only, so this distinction should be explicit.
- Do the authors want the feasible finite-cell procedures to be read as implementable guidance for discrete covariates, or primarily as minimax attainability benchmarks? The text contains both interpretations; one sentence in the discussion could fix the intended emphasis.

