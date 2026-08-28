# Learning Policies When Overlap Fails Near the Decision Boundary

This paper calibrates the minimax regret exponent for offline policy learning when weak overlap and small treatment effects occur together.

---

## The rate is set by three local quantities

- The target is observed-law welfare regret for deterministic treatment rules.
- Regret comes from assigning the wrong treatment where the conditional contrast \(\tau_P(X)\), the treatment-effect contrast, has a sign.
- The hard region has three scales: small contrast, small covariate mass, and rare observation of the informative treatment arm.
- Joint margin-overlap decay changes the usual margin rate by adding the weak-arm exponent \(\beta_{\alpha,\gamma}\).
- The lower-bound exponent is \(r_\star(\alpha,\gamma)\), and the clipped AIPW rule attains the same exponent when nuisance learning and clipping are nonbinding.

@informal thm:minimax-lower: Under the stated law-class and witness-calibration conditions, minimax regret is at least a constant times \(n^{-r_\star(\alpha,\gamma)}\).

---

## The empirical problem is ordinary, until overlap weakens

- Think of a retrospective treatment dataset with covariates \(X\), treatment \(A\), and bounded outcome \(Y\).
- A policy \(\pi\) maps each covariate value to treatment 0 or 1.
- The oracle treats exactly where the contrast \(\tau_P(x)\) is nonnegative.
- Under strict overlap, both treatment arms are observed often enough throughout the covariate space.
- Here, the informative arm can become rare precisely where the treatment decision is already hard.

@figure offline-policy-loop: Boxes labeled offline observations, nuisance estimates, clipped AIPW scores, empirical welfare maximization, learned deterministic policy, and welfare regret, connected in that order.

---

## Regret is weighted classification error

- Welfare is normalized to the contrast-weighted value of a policy.
- A policy loses welfare only on covariates where it disagrees with the oracle sign rule.
- Errors near \(\tau_P(x)=0\) matter less than errors with a large treatment contrast.
- This turns policy learning into classification with an econometric score and a welfare weight.

@formal def:welfare-regret

@informal thm:welfare-identity: Under bounded outcomes, regret equals the expected absolute treatment contrast on the policy-oracle disagreement set.

---

## The margin condition limits hard-but-important decisions

- The margin exponent \(\alpha\) controls how much covariate mass sits near zero contrast.
- Larger \(\alpha\) means fewer observations lie close to the decision boundary.
- In the running example, few patients have nearly tied treatment values when \(\alpha\) is large.
- Margin localization converts small regret into a small policy-oracle disagreement region.

@formal ass:margin

@informal thm:margin-localization: Under the margin, zero-effect, bounded-outcome, and disagreement-set conditions, disagreement probability is at most a constant times \(R_P(\pi)^{\alpha/(1+\alpha)}\).

---

## Overlap decay ties weak information to small contrasts

- The overlap score \(p_P(x)\) is the distance of the propensity score to the nearest endpoint.
- Weak overlap means one treatment arm is rarely observed at that covariate value.
- The parameter \(\gamma\) governs how weak overlap can concentrate inside the small-contrast region.
- In the running example, the rarer treatment arm is especially scarce for patients whose treatment effects are close to tied.

@formal ass:overlap-decay

@formal ass:strict-overlap-endpoint

---

## The exponent comes from the overlap envelope

- The margin condition allows an active block of mass \(h^\alpha\).
- A sign change on that block creates contrast scale \(h\).
- The overlap-decay condition allows the informative arm to appear with probability \(h^{\beta_{\alpha,\gamma}}\).
- The sample only sees the hard cell at scale \(h^\alpha h^{\beta_{\alpha,\gamma}}\).
- The resulting denominator is \(2+\alpha+\beta_{\alpha,\gamma}\).

@formal def:exponents

@formal prop:overlap-envelope

---

## The lower-bound construction hides one sign

- The two witness laws agree everywhere except on one treated active cell.
- On the active block \(B_n\), the contrast is either \(+h_n\) or \(-h_n\).
- Outside \(B_n\), both laws have the same strict positive contrast.
- The informative treatment arm is sampled with probability \(q_n\) on \(B_n\).
- The learner must infer which oracle policy is correct from rare, low-signal observations.

@figure two-point-witness: Boxes labeled common covariate law, active block, weak treatment arm, sign-positive law, sign-negative law, and oracle policy choice, with arrows showing that only the weak treatment arm on the active block separates the two laws.

@formal def:two-point-witness

---

## The witnesses belong to the target law class

- The construction satisfies bounded outcomes, positivity, margin, zero-effect, and overlap-decay restrictions.
- The two induced oracle policies disagree exactly on the active block.
- The policy class must contain the two witness actions used in the reduction.

@formal def:law-class

@informal lem:witness-membership: Under the stated calibration and smallness conditions, both witness laws lie in \(\mathcal P_{\alpha,\gamma}\) for all sufficiently large \(n\), and their oracle policies are the two stated block rules.

---

## Statistical closeness and welfare separation balance

- Divergence is small because the laws differ only on a low-mass, weak-arm, low-contrast cell.
- Regret separation is large enough because any single policy makes the wrong active-block decision under one of the two laws.
- Le Cam’s method converts this indistinguishability into a lower bound on minimax regret.

@informal lem:two-point-divergence: For the witness laws, the one-observation chi-square divergence is at most a constant times \(h_n^{2+\alpha+\beta_{\alpha,\gamma}}\), and the product divergence is bounded.

@informal lem:regret-separation: For every measurable policy, the larger regret under the two witness laws is at least a constant times \(h_n^{1+\alpha}\).

@informal lem:le-cam-two-point-chisq: Bounded product chi-square divergence gives every binary test a positive total error floor.

---

## The observed-law lower bound follows

@formal thm:minimax-lower

- The exponent is \(r_\star(\alpha,\gamma)=(1+\alpha)/(2+\alpha+\beta_{\alpha,\gamma})\).
- With strict overlap, \(\beta_{\alpha,\gamma}=0\), recovering the margin-driven denominator \(2+\alpha\).
- With positive overlap decay, \(\beta_{\alpha,\gamma}\) adds the information loss from rare observation of the informative arm.

---

## The analyzed rule is clipped cross-fitted AIPW ERM

- The nuisance triple \(\eta=(\mu_0,\mu_1,e)\) contains outcome regressions and the propensity score.
- Clipping replaces the propensity by a value inside \([q,1-q]\).
- Cross-fitting evaluates each fold using nuisance estimates trained away from that fold.
- The policy maximizes the clipped AIPW empirical welfare criterion over a countable dense policy skeleton.

@formal def:clipped-propensity

@formal def:clipped-aipw-score

@formal def:feasible-erm

---

## Clipping creates the upper-bound tradeoff

- Smaller \(q_n\) uses more weak-overlap data and increases the empirical-process envelope.
- Larger \(q_n\) stabilizes weights and increases clipping drift.
- The localization window \(u_n\) isolates the small-contrast region where overlap decay applies.
- The feasible exponent optimizes these choices for a fixed nuisance regime \((a,c)\).

@formal def:feasible-rate

@formal def:upper-risk

---

## The rule has a conditional upper exponent

@formal oeq:feasible-upper

- In the nonbinding branch, \(r_{\mathrm{up}}=r_\star(\alpha,\gamma)\) up to logarithmic factors.
- In the binding branch, \(r_{\mathrm{up}}\) is the nuisance-limited exponent delivered by this clipped AIPW ERM.
- The side-condition domain includes supplied nuisance rates, bounded cross-fitted nuisances, fixed balanced folds, and localized empirical-process assumptions.

---

## The proof separates stochastic error from drift

- Near-ERM gives a basic inequality against the oracle comparator.
- The clipped score envelope turns clipping level \(q_n\) into stochastic complexity.
- The drift identity expresses the conditional mean error of the clipped score.
- Localization places the weak-overlap drift inside the small-contrast region.
- The balance lemma converts all terms into the exponent \(r_{\mathrm{up}}\).

@informal lem:feasible-erm-basic-inequality: The feasible ERM is measurable and nearly maximizes empirical welfare, giving the stated comparator inequality.

@informal lem:crude-clipped-score-envelope: Under bounded outcomes and bounded outcome nuisances, the clipped AIPW score is at most a constant over \(q\).

@informal lem:clip-bias: The clipped AIPW score reproduces the contrast up to the explicit drift \(b_q\).

---

## Also in the paper

@informal lem:localized-clipped-drift-bound: The clipped-score drift is bounded by the stated product, weak-overlap localization, and complement terms when \(\gamma>0\), and by the product nuisance term under strict overlap.

@informal lem:crude-localized-master-bound: The regret of the clipped cross-fitted AIPW ERM is bounded by the lower-bound scale, the clipped empirical-process term, and the nuisance-drift terms.

@informal lem:clip-balance-exponent: The deterministic clipping and localization schedules make the master-bound terms at most \(C n^{-r_{\mathrm{feas}}}(\log n)^p\).

@informal lem:localized-vc-self-bound: An offset empirical-process control at scale \(\rho_n\) implies expected regret at the same scale.

@informal lem:crossfit-localized-offset-control: Fixed balanced cross-fitting preserves the localized offset control at the stated margin exponent.

@informal lem:clipped-region-localization: Under positive overlap decay, the weak-overlap part of any disagreement set is bounded by the stated margin-overlap and regret-localization terms.

---

## The open question is feasible tightness

@formal oeq:feasible-tight

- The lower bound calibrates the observed-law converse exponent over \(\mathcal P_{\alpha,\gamma}\).
- The upper bound characterizes one clipped cross-fitted AIPW ERM under explicit side conditions.
- The nonbinding regime gives matching polynomial exponents up to logarithmic factors.
- The strict-gap regime identifies the nuisance-learning branch that governs this procedure’s conditional rate.
