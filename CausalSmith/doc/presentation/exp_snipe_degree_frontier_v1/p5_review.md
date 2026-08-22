# Referee review

**Recommendation:** minor_revision
**Overall score:** 7.8/10 — The verified mathematical core delivers a sharp and useful minimax calibration, while the manuscript needs targeted prose repairs for comparison scope, cross-reference hygiene, and a few stale or confusing exposition points.

The paper establishes a finite-population minimax MSE frontier for known bounded-degree low-order polynomial interference under common Bernoulli assignment, with matched clipped-SNIPE upper bounds, complete-block lower constructions, exact complete-block SNIPE risks, and a block-local linear benchmark. The contribution is technically meaningful for design-based network experiments and is well aligned with the verified statements. Publication is plausible after focused revisions that sharpen the comparison to prior SNIPE work, clean up presentation, and repair a few contract violations.

## Strengths
- Sharp two-envelope minimax frontier with explicit dependence on the complete-block score energy and the out-degree overlap factor.
- Useful exact complete-block calculations and local-linear benchmark that clarify the geometry behind SNIPE weights.
- The paper states fixed-parameter constants and boundary cases carefully in most places, including fair-coin cancellations and degree-zero conventions.
- Dedicated related-work section engages the main interference and SNIPE literatures early in the manuscript.

## Findings
- **[minor·prose] Related work** — The comparison to Cortez-Rodriguez, Eichhorn, and Yu is mostly careful, but the sentence "their SNIPE analysis supplies design-unbiasedness and a stated worst-case worst-case variance upper bound whose degree dependence enters through \(d^{\beta}\)" contains a typo and leaves the exact comparator too imprecise for a central novelty claim.
  - *Fix:* Replace the sentence with a precise description of the cited theorem's assumptions, normalization, and displayed degree factor; remove the duplicated "worst-case" and state that the present result calibrates the bounded known-graph class against that stated upper bound.
- **[minor·prose] Main results** — The theorem map says "Exact complete-block SNIPE risk" and "canonical unprojected SNIPE on complete directed blocks" but the surrounding prose also says the result is "globally" exact for that estimator. A reader could miss that exactness is for the worst-case risk of the fixed estimator when \(d\mid n\), not the exact all-estimator minimax constant.
  - *Fix:* Add one clarifying sentence after the theorem map: the exact equality concerns canonical unprojected SNIPE's worst-case risk on the fixed block graph and the global supremum over the two classes when \(d\mid n\); the all-measurable minimax leading constant is addressed only by the rate bounds.
- **[minor·prose] Verification note** — The sentence "where a result from the literature is a formal dependency, it enters as a published input rather than a Lean-checked step" in the author footnote is stale relative to the verification contract for this submission, which records no external formal dependencies for the displayed objects.
  - *Fix:* Update the author footnote and verification-note wording to match the current contract: the displayed formal statements and proofs are Lean-verified, and cited work supplies econometric framing, terminology, and positioning for these objects.
- **[minor·structure] Appendices** — Several appendix proof paragraphs present long informal derivations for theorem statements already declared verified. This is acceptable, but the main text does not give readers a short proof roadmap before entering very lengthy proof blocks.
  - *Fix:* At the start of the appendix, add a compact roadmap listing which verified declarations establish the representer identity, overlap count, Hellinger bound, minimax frontier, bounded-outcome frontier, local-linear benchmark, and fair-coin specialization.
- **[minor·statement] Setup and assumptions** — The score definition uses \(\bar\beta_d\) in the outer sum for every unit and then explains the empty-sum convention for units with \(|N_i|<\bar\beta_d\). This is correct, but it is less transparent than the Lean declaration, which sums to \(\min\{\beta,|N_i|\}\).
  - *Fix:* Rewrite \cref{obj:def:snipe-score} with outer limit \(\min\{\beta,|N_i|\}\), then mention that this equals the displayed block limit when \(|N_i|=d\).
- **[minor·structure] Related work** — The related-work section cites many strands, but the closest comparison would benefit from a small displayed rate table or paragraph aligning assumptions across the prior SNIPE theorem, the present coefficient-mass class, and the bounded-outcome class.
  - *Fix:* Add a short comparison table with columns for graph knowledge, assignment design, outcome class, estimator, target, and risk or variance rate; keep the text explicit that the present result sharpens the bounded-class calibration rather than the prior paper's unrestricted theorem.
- **[nit·prose] global** — House typography requires sentence case headings. The theorem and definition titles mostly comply, but title-like item labels such as "Coefficient-mass minimax frontier" and table headers are acceptable; ensure no remaining generated headings outside the excerpt are Title Case.
  - *Fix:* Run a heading pass over the full source and keep section/subsection titles in sentence case, preserving proper nouns and math symbols.
- **[nit·prose] Related work** — The phrase "a stated worst-case worst-case variance upper bound" is a copy-editing error.
  - *Fix:* Delete one occurrence of "worst-case".
- **[nit·prose] Main results** — The local-linear theorem includes the striking distance-equals-two construction, but the surrounding discussion gives only one sentence of interpretation. Readers may not immediately understand why this result belongs beside the minimax frontier.
  - *Fix:* Add one sentence before or after the theorem explaining that the construction separates asymptotic risk optimality from normalized pointwise closeness to the canonical representer within the block-local unbiased linear class.

## Questions for authors
- Can the closest-prior-work comparison state the exact theorem number, normalization, and degree factor from Cortez-Rodriguez, Eichhorn, and Yu so readers can verify the sharpening directly?
- Do the authors want the exact complete-block unprojected-SNIPE equality to be highlighted as an estimator-risk identity rather than as evidence about the all-measurable minimax constant?

