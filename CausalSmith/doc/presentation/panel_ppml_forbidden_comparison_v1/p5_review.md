# Referee review

**Recommendation:** major_revision
**Overall score:** 5.5/10 — The core deterministic sign-reversal result appears correct and potentially useful, but the manuscript is not yet strong enough for a leading econometrics journal because the empirical bridge, exposition of the central sign argument, and positioning remain underdeveloped.

The paper studies the pseudo-true treatment coefficient from a pooled unit-and-time fixed-effect PPML projection in staggered adoption designs and shows that it can be negative even when all granular proportional effects are positive. The verified formal statements deliver the advertised population sign reversal and the contrast with a positive counterfactual-share PTT. As written, however, the contribution is narrower than the paper's applied framing suggests, and several central objects and proof steps need clearer exposition before the paper would be publishable.

## Strengths
- The main population result is sharp, clean, and directly addresses a natural nonlinear analogue of forbidden comparisons in staggered DiD.
- The paper is careful to distinguish the pseudo-true PPML projection from positive-weight proportional treatment targets.
- The four-cohort witness is transparent and removes several possible confounds, including unequal shares and nonflat untreated means.
- The manuscript is unusually explicit about what it does not prove: sampling consistency, inference, and estimation of granular effects.

## Findings
- **[major·prose] intro/setup/discussion** — The empirical bridge remains incomplete. The manuscript says, "This is the population analogue of the coefficient an applied pooled unit-and-time fixed-effect PPML regression is trying to summarize," while later conceding that "No theorem below connects that sample coefficient to beta_N^star(delta) or beta^star(delta), and no sampling inference is developed." This is honest, but for a leading econometrics journal it leaves the main applied relevance under-supported.
  - *Fix:* Either add a formal sample-to-population result for the fixed-effect PPML coefficient, including the high-dimensional fixed effects and separation/selection issues, or substantially narrow the framing so the paper is presented as a deterministic projection note rather than as a diagnosis of what applied PPML regressions estimate.
- **[major·structure] main results/appendix** — The proof exposition of the central global sign result is too compressed. The key step says, "At the frontier fit with treatment coefficient set to zero, the nuisance scores vanish and the treatment score is Phi/(T M)," but the manuscript does not give readers a self-contained derivation of this frontier fit or the concavity/score-crossing argument that turns the score sign into the sign of beta^star.
  - *Fix:* Add a transparent lemma or proof subsection deriving the beta=0 nuisance fit, computing the treatment score as Phi/(T M), and explaining why strict concavity implies sign(beta^star)=sign(Phi). The formal result may be verified, but the paper still needs a readable econometric argument.
- **[major·other] discussion** — The paper establishes that the sign-reversal region is nonempty, but it gives little sense of how economically relevant the region is. The statement that the example is "relevant for otherwise conventional staggered-adoption designs" is stronger than the current evidence, since the manuscript mostly presents one witness and the algebraic frontier.
  - *Fix:* Add a numerical or analytical exploration of the reversal region under plausible cohort shares, untreated means, and effect heterogeneity. At minimum, graph the four-cohort frontier and discuss how large the exceptional cell effect must be relative to the others; preferably include calibrated simulations from common staggered-adoption designs.
- **[minor·structure] setup/main results** — The proportional PTT objects are not defined early enough for the theorem-level contrast to be fully self-contained. Symbols such as B_obs, tau, omega, and PTT appear in Theorem 3, but the setup does not first give a formal definition of the counterfactual-share target and its weights.
  - *Fix:* Add a short definition before the main theorem defining B_obs, tau_gt, omega_gt, H, and PTT, then state the theorem as a comparison between beta^star and that already-defined target.
- **[minor·citation] related literature** — The closest-literature positioning is directionally right but still too general. The Moreau-Kastler and Wooldridge comparisons should state more explicitly that existing nonlinear DiD or proportional PTT results do not provide a sign characterization of the misspecified pooled FE-PPML projection coefficient.
  - *Fix:* Revise the related-work paragraph to isolate the precise novelty: not proportional-effect identification, not PPML consistency, and not a positive-weight ATT, but a sign characterization of the pooled pseudo-true PPML treatment coordinate under heterogeneous proportional effects.
- **[minor·prose] global** — Notation and cross-references remain somewhat unstable. Examples include switching between gamma_t and gamma_t0, referring to "Section~ref{obj:ass:cohort-share-limit}" when the target is an assumption, and introducing finite-array and collapsed projections before giving a concise verbal map of why both are needed.
  - *Fix:* Standardize notation throughout, correct assumption/section references, and add a short roadmap in the setup explaining the roles of the finite-array object, the collapsed object, and the limiting sign calculation.

## Questions for authors
- Do you intend the paper to make a claim about the probability limit of the actual sample FE-PPML coefficient, or only about the deterministic collapsed projection?
- How large is the sign-reversal region under empirically plausible effect heterogeneity, beyond the displayed four-cohort witness?
- Can the PTT comparison be stated using a fully defined target in the setup rather than introduced inside the theorem?
