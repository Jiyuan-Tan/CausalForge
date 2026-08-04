# Referee review

**Recommendation:** minor_revision
**Overall score:** 8/10 — The paper delivers a sharp and formally verified minimax characterization with clear novelty, while needing targeted exposition and positioning repairs before publication.

The submission studies finite-population design-based estimation of all-treated-versus-all-control effects under known bounded-degree low-order network interference and Bernoulli assignment. The verified results establish matched minimax MSE frontiers, a complete-block least-favourable construction, a bounded-outcome extension, and an exact local-linear benchmark. I view the contribution as publishable and useful for econometric work on network experiments, provided the authors tighten several scope, notation, and positioning points.

## Strengths
- The minimax frontier gives an explicit and interpretable degree dependence through the overlap factor and complete-block energy.
- The paper connects estimator construction, lower-bound priors, and local-linear optimality through a common Riesz/energy object.
- The theorem statements are precise and the verification contract supports the main mathematical claims.
- The bounded-outcome and fair-coin specializations help translate the abstract energy expression into familiar rate statements.

## Findings
- **[minor·prose] abstract** — The sentence "For fair-coin assignment, only odd interaction orders contribute to A_d; in the degree-one case the frontier becomes B^2\min\{1,d^2/n\}" is ambiguous because the paper uses d for graph degree, while this sentence appears to mean interaction order beta=1.
  - *Fix:* Rewrite as "For fair-coin assignment, only odd interaction orders contribute to A_d; for first-order interactions (beta=1), the frontier becomes B^2\min\{1,d^2/n\}."
- **[minor·prose] intro** — The sentence "The first is the complete-block score energy A_d in \cref{obj:def:block-score-energy}. The block score represents the all-treated-versus-all-control contrast on the low-order polynomial space, so A_d is the minimum energy of an unbiased local weight..." attributes the representer and minimum-energy facts to the definition rather than the lemma that proves them.
  - *Fix:* Point the representer/minimum-energy claim to \cref{obj:lem:block-energy-representer} and state the scope: complete-block product Bernoulli designs and the low-order polynomial space \mathcal P_d.
- **[minor·prose] Main Results** — The theorem titled "Bounded-Outcome Degree Frontier" proves the bounded-outcome minimax rate through the chain R_{n,\ell_1}^\star \le R_{n,\infty}^\star plus the upper bound, but the surrounding prose says the theorem "establishes the same minimax order" without explicitly reminding the reader that the lower bound is inherited from the contained coefficient-mass class.
  - *Fix:* Add one sentence immediately after the theorem explaining that the bounded-outcome lower bound follows from carrierwise containment of the coefficient-mass class and the coefficient-class lower frontier.
- **[minor·structure] Setup and Assumptions** — The paper introduces many symbols and synthesized objects in rapid succession, including L^2(P_Z), \mathcal P_d, L_d, A_i, \Pi_+, and \Pi_-, before the reader has a compact map of how they are used.
  - *Fix:* Add a short notation table or paragraph grouping objects by role: global decision problem, block Riesz problem, least-favourable priors, and local-linear benchmark.
- **[minor·citation] Discussion and Extensions** — The paper positions the results against the closest SNIPE and low-order interference literature, but it gives little concrete comparison of what changes relative to Cortez-Rodriguez, Eichhorn, and Yu beyond "matched minimax upper and lower bounds with explicit degree dependence."
  - *Fix:* Add a concise comparison paragraph stating which part of the prior SNIPE analysis is reused, which risk criterion and model class are new here, and how the dA_d/n frontier differs from previously available variance or consistency results.
- **[nit·prose] Main Results** — Several cross-references are wrapped in math mode, e.g. "Under the notation in \(\cref{obj:def:exposed-order,obj:def:minimax-risk,obj:def:model-class}\)". This compiles but makes reader-facing references visually inconsistent with surrounding prose.
  - *Fix:* Use ordinary text-mode cleveref commands, e.g. "Under the notation in \cref{obj:def:exposed-order,obj:def:minimax-risk,obj:def:model-class}".

## Questions for authors
- Can the authors add a short worked example for beta=1 and p=1/2 showing how the overlap factor d and energy A_d combine into d^2/n?
- Will the public replication package expose the Lean declarations corresponding to the verification note and the exact manuscript commit?

