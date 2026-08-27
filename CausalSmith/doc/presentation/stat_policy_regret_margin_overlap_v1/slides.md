# Calibrating Weak Overlap in Offline Policy Learning

This paper shows how joint margin-overlap decay changes the best possible welfare-regret exponent, and analyzes when a clipped cross-fitted AIPW rule reaches that benchmark.

---

## Punchline

- Offline policy learning is easiest when mistakes happen only where treatment effects are small.
- It becomes harder when those same covariate regions also have weak treatment-arm information.
- The paper calibrates that interaction through the exponent \(\beta_{\alpha,\gamma}\).
- The minimax lower-bound exponent is \(r_\star(\alpha,\gamma)\).
- Under stated nuisance-rate and empirical-process side conditions, a specified clipped cross-fitted AIPW ERM matches that exponent up to logarithmic factors whenever nuisance learning and clipping are not the binding constraint.
- In nuisance-limited regimes, the same conditional analysis gives the rule’s exponent.

---

## The Question

- We observe offline data \(O=(X,A,Y)\).
- A policy \(\pi(X)\) chooses treatment \(0\) or \(1\).
- The goal is low welfare regret: choose the treatment whose conditional contrast has the right sign.
- Running example: a treatment is valuable for some patients, harmful for others, and nearly neutral near a clinical boundary.
- The hard region is where the treatment contrast is small.
- The new feature here is that the rare treatment arm can also be rare in that same region.

---

## Why Weak Overlap Changes Rates

- Under regular overlap, the policy problem resembles margin-based classification.
- Small effects create a margin region, and mistakes there cost little.
- Under joint margin-overlap decay, the data are least informative exactly near that margin.
- The lower-bound witness makes the informative treatment arm appear with probability \(q_n\) on a small active block.
- The statistical question becomes: how small can the contrast be while the two signs remain hard to distinguish?

@figure margin-overlap-block: How the lower-bound witness is built: a small active block \(B_n\) carries a local contrast of size \(h_n\) whose sign is revealed only by a treatment arm appearing with probability \(q_n\), a weakness that joint decay caps.

---

## Setup in Words

- The observed law \(P\) defines \(e_P(x)\), the propensity score, and \(\mu_a(x)\), the treatment-arm outcome means.
- The treatment contrast is \(\tau_P(x)=\mu_1(x)-\mu_0(x)\).
- The overlap score is \(p_P(x)=\min\{e_P(x),1-e_P(x)\}\), the distance to the nearest propensity boundary.
- Welfare compares policies by \(E_P[\pi(X)\tau_P(X)]\).
- The oracle policy treats exactly where \(\tau_P(x)\ge0\).

@formal def:welfare-regret

---

## Margin and Overlap Assumptions

- The margin condition limits how much covariate mass has small nonzero \(|\tau_P(X)|\).
- Zero-effect agreement makes ties welfare-neutral for the policy class.
- The overlap-decay condition limits how often weak overlap and small contrast occur together.
- In the running example, rare treatment assignment is allowed near the clinical boundary, but its mass is controlled jointly with the small-effect region.

@formal ass:margin

@formal ass:overlap-decay

---

## Policy Class and Law Class

- Policies are deterministic binary rules in a finite-VC class.
- A countable dense skeleton makes empirical maximization measurable.
- The law class \(\mathcal P_{\alpha,\gamma}\) collects bounded outcomes, positivity, the margin restriction, zero-effect convention, overlap decay, and the strict-overlap endpoint for \(\gamma=0\).
- The exponent \(r_\star(\alpha,\gamma)\) is the benchmark rate produced by the margin-overlap calibration.

@formal ass:policy-class

@formal def:exponents

---

## Key Idea

- The lower bound balances three quantities.
- The active block has mass \(h_n^\alpha\), matching the margin condition.
- The local contrast has size \(h_n\), so a wrong sign costs \(h_n^{1+\alpha}\).
- The informative treatment arm appears with probability \(q_n=h_n^{\beta_{\alpha,\gamma}}\) when overlap decay permits it.
- The two laws stay hard to distinguish when \(n h_n^{2+\alpha+\beta_{\alpha,\gamma}}\) is bounded.

@informal prop:overlap-envelope: For \(\gamma>0\), within the tight-window calibration, \(\beta_{\alpha,\gamma}\) is the largest weak-arm exponent compatible with a block of margin mass \(h^\alpha\).

---

## Where the Literature Stands

- Treatment-choice work frames policy learning as welfare maximization under sampling uncertainty.
- Empirical welfare maximization gives finite-sample regret tools for structured policy classes.
- Doubly robust and cross-fitted scores provide the feasible estimation architecture.
- Margin-based classification explains how small decision-boundary mass improves regret.
- Limited-overlap work explains why inverse-propensity methods become unstable near propensity boundaries.
- This paper combines the margin and overlap mechanisms in a single observed-law minimax calibration.

---

## Main Lower Bound

@informal thm:minimax-lower: Over \(\mathcal P_{\alpha,\gamma}\), every measurable policy estimator has worst-case expected regret at least a constant times \(n^{-r_\star(\alpha,\gamma)}\) for all sufficiently large \(n\).

@formal thm:minimax-lower

---

## What the Lower Bound Means

- Under strict overlap, \(\beta_{\alpha,\gamma}=0\), so the exponent is the familiar margin-driven benchmark.
- With positive overlap decay, \(\beta_{\alpha,\gamma}\) enters the denominator.
- The rate reflects the probability of observing the arm that reveals the sign on the margin block.
- In the running example, the lower bound says the hardest cases concentrate weak assignment precisely near clinically marginal patients.

@informal thm:welfare-identity: Welfare regret is exactly contrast-weighted disagreement with the oracle policy.

@informal thm:margin-localization: Under the margin and zero-effect conditions, low regret implies a small oracle-disagreement region.

---

## The Feasible Rule

- The procedure estimates the contrast with a clipped AIPW score.
- Clipping replaces propensities by values in \([q_n,1-q_n]\).
- Cross-fitting evaluates each observation with nuisance estimates trained away from its fold.
- The empirical rule maximizes clipped AIPW welfare over the countable policy skeleton.
- The tuning schedule balances stochastic fluctuation, clipping, and nuisance drift.

@formal def:clipped-aipw-score

@formal def:feasible-erm

---

## Feasible Upper Bound

@informal oeq:feasible-upper: Under the stated nuisance-rate, cross-fitting, boundedness, and localized empirical-process side conditions, the clipped cross-fitted AIPW ERM has conditional upper risk at most \(C n^{-r_{\mathrm{up}}}(\log n)^p\).

@formal oeq:feasible-upper

---

## Why the Novelty Wins

- A naive un-clipped AIPW rule can have a large envelope when propensities approach a boundary.
- A fixed clip controls variance but can create drift on weak-overlap regions.
- The paper lets \(q_n\) shrink and pairs it with a contrast window \(u_n\).
- The master bound balances \((nq_n^2)^{-A_\alpha}\), \(r_{\mu,n}r_{e,n}/q_n\), \(r_{\mu,n}u_n^{\alpha/2}q_n^{1/(2\gamma)}\), and \(r_{\mu,n}^2/u_n\).
- The optimized exponent is \(r_{\mathrm{up}}=\min\{r_\star(\alpha,\gamma),g_{\mathrm{joint}}(\alpha,\gamma,a,c)\}\).
- So the nuisance-and-clipping exponent \(g_{\mathrm{joint}}\) binds exactly when it falls below \(r_\star(\alpha,\gamma)\); otherwise the minimum returns \(r_\star(\alpha,\gamma)\) itself.

@formal def:feasible-rate

---

## Also in the Paper

@informal lem:feasible-erm-basic-inequality: The feasible ERM is measurable and satisfies the near-maximization inequality needed to compare it with any in-class policy.

@informal lem:crude-clipped-score-envelope: The clipped AIPW score has envelope at most order \(1/q\).

@informal lem:localized-clipped-drift-bound: The clipped-score drift is bounded by the product nuisance remainder, the localized weak-overlap term, and the localization-complement term.

@informal lem:crude-localized-master-bound: The expected regret of the clipped AIPW ERM is bounded by the lower-bound scale, the clipped empirical-process term, and the nuisance-drift terms.

@informal lem:clip-balance-exponent: The chosen clipping and localization schedules make the master-bound terms at most \(C n^{-r_{\mathrm{feas}}}(\log n)^p\).

---

## Why the Lower Bound Is True

- Construct two observed laws that agree everywhere except on a small active block.
- On that block, the treatment contrast has opposite signs under the two laws.
- The informative treatment arm is sampled rarely there, according to the overlap-margin calibration.
- The product distributions remain close, so no test reliably recovers the sign.
- Any policy must choose one assignment on the active block, so it incurs regret under at least one law.

---

## Why the Upper Bound Is True

- The ERM inequality turns empirical near-optimality into a regret comparison with the oracle policy.
- The clipped score envelope controls stochastic fluctuation through localized VC bounds.
- The drift identity isolates the conditional bias of the clipped and estimated score.
- The overlap-decay condition localizes weak-overlap drift to the small-contrast region.
- The tuning schedule chooses clipping and localization exponents to balance the four leading terms.

---

## Takeaways

- The paper establishes an observed-law minimax lower-bound exponent for offline policy learning under joint margin-overlap decay.
- The exponent is calibrated by margin mass, local contrast size, and weak treatment-arm probability.
- Under the stated nuisance-rate and empirical-process side conditions, a clipped cross-fitted AIPW ERM matches the lower-bound exponent up to logarithmic factors whenever \(g_{\mathrm{joint}}\) does not bind.
- When \(g_{\mathrm{joint}}\) binds, the same conditional analysis gives the specified rule’s nuisance-limited exponent.
- The paper records the remaining feasible-tightness question explicitly.

@formal oeq:feasible-tight
