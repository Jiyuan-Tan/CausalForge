# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The paper delivers a verified and substantively useful minimax characterization, with remaining issues concentrated in exposition, scope wording, and reference hygiene rather than mathematical validity.

The submission establishes minimax mean-squared-error frontiers for design-based total-effect estimation under bounded-degree, low-order network interference, with clipped SNIPE attaining the upper bound and complete-block constructions furnishing matching lower bounds. The verified statements support the central rate claims and the complete-block local-linear benchmark. The paper is publication-worthy after tightening several prose claims and improving the reader-facing organization.

## Strengths
- The main minimax frontier has clear econometric value for known-graph Bernoulli network experiments.
- The paper connects SNIPE variance calculations, complete-block Riesz representers, and least-favourable priors in a coherent way.
- The formal verification contract gives unusually strong assurance for the finite-design algebra and stated theorem claims.
- The fair-coin and first-order specialization provides a useful calibration of the degree cost.

## Findings
- **[minor·prose] Setup and Assumptions** — The prose says the projected SNIPE estimator "clips that average to the coefficient-mass target range." Under the coefficient-mass envelope the all-treated-versus-all-control target is naturally bounded at scale 2B, while the verified coefficient-class estimator is projected to [-B,B] and the proof uses this as a scale-preserving bounded projection rather than the full target range.
  - *Fix:* Rewrite the sentence to say that the projected estimator clips the SNIPE average to [-B,B] for the coefficient-mass risk comparison. Reserve "natural total-effect range" for the bounded-outcome projection to [-2B,2B], or explicitly state the coefficient-class target-scale bound used by the theorem.
- **[minor·structure] Setup and Assumptions** — The notation map is helpful, but the setup still introduces many objects in quick succession, including the prior laws, block programs, local-linear sequence, and bounded-outcome class before the reader reaches the main theorem logic.
  - *Fix:* Move the synthesized prior-predictive laws and some local-linear notation to the point where they are used, or add a compact table with columns for object, role, and first theorem using it. Keep the main setup focused on the design, model classes, estimator, risk, and block energy.
- **[minor·prose] Introduction / Discussion and Extensions** — The comparison with Cortez-Rodriguez, Eichhorn, and Yu is directionally accurate but still compressed. The manuscript states that the present paper "sharpens" that setting, but readers would benefit from a more concrete division between the antecedent estimator/variance analysis and the present minimax, lower-bound, bounded-outcome, and local-linear contributions.
  - *Fix:* Add 2-3 sentences specifying what CREY already supplies and what this paper adds: matched minimax lower bounds, the explicit dA_d/n or d choose(d,k*) degree frontier, the complete-block least-favourable construction, and the exact local-linear benchmark.
- **[nit·prose] Main Results** — Several reader-facing cross-references are wrapped in math mode, for example "Under the notation in \(\cref{obj:def:exposed-order,obj:def:minimax-risk,obj:def:model-class}\)". This is visually inconsistent with the cleveref-only cross-reference convention.
  - *Fix:* Remove math-mode wrappers around prose cross-references throughout the manuscript: use "Under the notation in \cref{...}" and the corresponding \Cref form at sentence starts.
- **[nit·prose] abstract / Main Results** — The phrase "degree-one" can still be read as graph degree one because d denotes graph degree throughout the paper, even though the intended specialization is interaction order beta=1.
  - *Fix:* Use "first-order interactions (beta=1)" in theorem subtitles and surrounding prose, for example rename the fair-coin item to "First-order interaction minimax frontier."

## Questions for authors
- Is the coefficient-class projection to [-B,B] intended purely as a bounded scale projection, while the full total-effect range remains [-2B,2B]?

