# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The verified results deliver a clear minimax frontier for a meaningful transported-IV weak-ratio problem, with remaining issues mainly in exposition, scope calibration, and literature presentation rather than correctness.

The paper studies honest confidence sets for a transported complier average causal effect when the transported first stage may be weak and transport weights may be dispersed. Its central contribution, a matched expected-length frontier of order min{1,t0^{-1/2}} indexed by n mu_n^2/kappa_n, is substantively interesting and appears faithfully supported by the verified theorem statements. The manuscript is now largely coherent, but it still needs tighter explanation of the integrated receipt-transport condition, cleaner separation between formal verification and expository proof narrative, and more scannable positioning against the closest literature.

## Strengths
- The main frontier is sharp, interpretable, and tied to a natural effective-strength index combining first-stage weakness and transport-weight dispersion.
- The paper connects transported noncompliance with weak-IV robust score inversion in a way that should interest econometricians working on external validity, LATE, and weak identification.
- The finite-cell feasible results are valuable because they show how target covariate sampling can learn the relevant dispersion scale while preserving the oracle order under stated growth conditions.
- The prose generally represents the verified theorem statements accurately and keeps theorem conditions visible.

## Findings
- **[minor·prose] Setup, Transport, and Honest Risk** — The interpretation of target-average receipt transport is improved, but the empirical content remains high-stakes because the denominator is identified from an average cross-population compliance restriction rather than a conditional one. The current example lists possible supporting data sources but still leaves the reader without a compact diagnostic for what evidence validates the integrated equality in applications.
  - *Fix:* After the appointment-reminder example, add a short affirmative diagnostic paragraph stating that the assumption is supported by evidence that the target-law average compliance margin from target adherence/receipt data agrees with the source conditional first-stage contrast averaged over target covariates; explicitly distinguish this average restriction from conditional receipt-contrast transport.
- **[minor·structure] appendix** — The verification note says the appendix records machine-checked statements, but the long proof narratives include inline comments such as "% lean: compact_causal_range" throughout. This blurs the boundary between the formal artifact and the reader-facing proof explanation.
  - *Fix:* Move the inline Lean declaration comments into a compact verification table or margin note at the start of the appendix, and keep the proof narratives as ordinary mathematical exposition tied to theorem names through \cref commands.
- **[minor·prose] Related Literature and Discussion** — The sentence beginning "Among transported-noncompliance papers, the closest transported-CACE comparison is \citet{ChenHuang2025}" remains dense: it combines the nearest transported-CACE paper, transported encouragement/adherence papers, weak-IV LATE papers, and two-sample IV papers in one block, making the novelty claim harder to audit.
  - *Fix:* Replace the dense paragraph with a short comparison table or separate sentences for Chen--Huang, Rudolph--van der Laan/Ross, Ma/Smucler et al., and Choi--Gu--Shen/Choi--Shen, with columns or clauses for estimand, design, inference target, and how the present frontier differs.
- **[nit·prose] Oracle Frontier and Score Inversion** — The phrase "rather than by studentizing a ratio" frames the method through what it avoids, outside a limitations or future-work section. This is a small violation of the affirmative contribution-framing contract.
  - *Fix:* Rewrite affirmatively, for example: "Weak-IV robust confidence sets are naturally built by inverting a reduced-form score restriction, following the same principle behind Anderson--Rubin and Fieller inference."
- **[nit·statement] Fixed Geometry and Feasible Cell Weight Learning** — The theorem title "Finite-cell weight attainment" is slightly underspecified: the theorem establishes feasible sample-only score-inversion attainment with target empirical cell frequencies and a collision-scale dispersion proxy, not merely weight attainment.
  - *Fix:* Rename the theorem title to something like "Feasible uniform-cell score attainment" or "Finite-cell target-weight learning attainment" so the heading signals both feasibility and the inversion procedure.

## Questions for authors
- Can the empirical support for integrated receipt-contrast transport be summarized as a practical diagnostic or sensitivity target in applications?
- Do the authors intend the appendix proof narratives to be read as independent mathematical proofs, or as expository guides to the Lean declarations?

