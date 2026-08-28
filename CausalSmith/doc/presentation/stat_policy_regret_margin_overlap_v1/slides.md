# Calibrating Regret Under Weak Overlap

Offline policy learning becomes statistically harder when the treatment arm needed to learn small welfare-relevant contrasts is also rarely observed.

---

## Overview

- We study deterministic treatment rules learned from offline observational data.
- Welfare regret is measured from the observed-law treatment contrast \(\tau_P(x)\), the conditional gain from treatment.
- The law class links two local difficulties: small contrasts and weak overlap.
- The minimax lower bound gives the benchmark exponent \(r_\star(\alpha,\gamma)\).
- A clipped cross-fitted AIPW (augmented inverse propensity weighting) empirical welfare rule attains the benchmark exponent when nuisance and clipping terms are nonbinding.

@informal thm:minimax-lower: Over the joint margin-overlap law class, worst-case regret is at least order \(n^{-r_\star(\alpha,\gamma)}\).

---

## Motivation

- A policymaker has logged treatment data and wants a rule for who should receive treatment.
- Think of a job-training program assigned with observational discretion.
- For some workers, the earnings gain is close to zero.
- Among those workers, the historical assignment rule may place almost everyone in one arm.
- The target remains the welfare loss from assigning the wrong treatment.
- The statistical difficulty is learning the sign of a small contrast with few observations from the informative arm.
- The question is how this joint scarcity changes the best possible regret rate.

---

## Setup

- One observation is \(O=(X,A,Y)\): covariates, binary treatment, bounded outcome.
- The propensity \(e_P(x)\) is the treatment probability under the observed law.
- The overlap score \(p_P(x)\) is the distance of \(e_P(x)\) to the nearest propensity boundary.
- The treatment contrast \(\tau_P(x)\) is the conditional mean outcome under treatment minus control.
- A deterministic policy \(\pi\) assigns treatment as a function of \(X\).

@formal def:welfare-regret

---

## Regret as weighted classification

@informal thm:welfare-identity: Welfare regret is exactly the contrast-weighted probability of disagreeing with the oracle treatment rule.

@formal thm:welfare-identity

- A wrong decision where \(|\tau_P(X)|\) is large is costly.
- A wrong decision near \(\tau_P(X)=0\) has little welfare cost.
- This identity lets us use margin logic from classification.

---

## Margin and overlap

- The margin exponent \(\alpha\) controls how much covariate mass has a small nonzero treatment contrast.
- The overlap-decay exponent \(\gamma\) controls how weak overlap can concentrate inside that small-contrast region.
- Under strict overlap, \(\gamma=0\) and the overlap score stays bounded away from zero.
- Under positive overlap decay, weak treatment-arm information is allowed near the decision boundary.

@formal ass:margin

@formal ass:overlap-decay

---

## Localizing mistakes

@informal thm:margin-localization: Under the margin condition, low-regret policies disagree with the oracle only on a small covariate region.

@formal thm:margin-localization

- This is the regret version of a low-noise classification localization.
- In the job-training example, a good rule can differ from the oracle mainly among workers with nearly zero gains.

---

## Related literature

- Manski (2004), Manski (2009), Stoye (2009), and Kitagawa and Tetenov (2018) frame treatment choice through welfare regret.
- Athey and Wager (2021) and Chernozhukov et al. (2018, 2022) motivate doubly robust and cross-fitted policy learning.
- Audibert and Tsybakov (2007), Massart and Nedelec (2006), and Tsybakov (2009) explain how margins accelerate excess-risk rates.
- Li et al. (2016), D'Amour et al. (2017), Ben-Michael and Keele (2022), Hill and Chaudhuri (2024), and Susmann et al. (2025) analyze weak-overlap behavior.
- Liu et al. (2026) is closest on clipping-based upper-bound analysis.

---

## Key idea

- Build two observed laws that agree almost everywhere.
- On a small active block \(B_n\), flip the sign of a tiny treatment contrast.
- Make the informative treatment arm rare on that same block.
- Any learner must choose one sign, and one of the two laws charges regret for that choice.

@figure margin-overlap-block: Box-and-arrow schematic showing covariates leading to an active block, local contrast, joint decay, weak arm information, hard sign learning, and the resulting rate question.

---

## Calibration

@informal prop:overlap-envelope: The overlap envelope makes \(\beta_{\alpha,\gamma}\) the largest weak-arm exponent compatible with a block of margin mass \(h^\alpha\).

@formal prop:overlap-envelope

- The denominator \(2+\alpha+\beta_{\alpha,\gamma}\) has three sources.
- The \(2\) is the cost of distinguishing two close conditional means.
- The \(\alpha\) is the margin mass of the active block.
- The \(\beta_{\alpha,\gamma}\) is the loss from rare informative-arm sampling.

---

## Lower-bound witness

@informal lem:witness-membership: The two local alternatives satisfy the observed-law class restrictions and induce opposite oracle choices on the active block.

@informal lem:two-point-divergence: The product distributions of the two alternatives remain statistically close at sample size \(n\).

@informal lem:regret-separation: Every policy incurs at least one of the two witness regrets at order \(h_n^{1+\alpha}\).

@informal lem:le-cam-two-point-chisq: A bounded chi-square product divergence gives a positive lower bound on testing error.

@figure two-point-witness: Box-and-arrow schematic showing a common covariate law, active block, weak treatment arm, two sign laws, and the oracle policy choice.

---

## Main result

@informal thm:minimax-lower: Under the stated margin-window, overlap-decay, and witness-calibration conditions, minimax regret is at least \(c n^{-r_\star(\alpha,\gamma)}\).

@formal thm:minimax-lower

- This is the observed-law converse benchmark for the class \(\mathcal P_{\alpha,\gamma}\).
- Strict overlap gives the usual margin-driven denominator.
- Joint margin-overlap decay adds the weak-arm exponent to the denominator.

---

## Feasible rule

- We also analyze one implementable empirical welfare rule.
- Estimate nuisance functions on folds held away from the evaluation fold.
- Clip the estimated propensity into \([q_n,1-q_n]\).
- Score each observation with the clipped AIPW contrast score.
- Choose the policy with nearly maximal clipped empirical welfare — the empirical risk minimization (ERM) step.

@figure offline-policy-loop: Box-and-arrow schematic showing offline observations, nuisance estimates, clipped AIPW scores, empirical welfare maximization, learned policy, and welfare regret.

---

## Upper-bound mechanics

@informal lem:clip-bias: The clipped AIPW score equals the treatment contrast plus an explicit drift term.

@informal lem:feasible-erm-basic-inequality: The feasible ERM satisfies the empirical welfare comparison inequality against any policy comparator in the class.

@informal lem:crude-clipped-score-envelope: Clipping at level \(q\) bounds the score envelope at scale \(1/q\).

@informal lem:localized-clipped-drift-bound: The clipped-score drift is controlled by product nuisance error, weak-overlap localization, and outcome-regression localization.

---

## Rate balance

@informal lem:crude-localized-master-bound: The regret of the clipped cross-fitted AIPW ERM is bounded by the lower-bound benchmark, the clipped empirical-process term, and three nuisance-driven terms.

@informal lem:clip-balance-exponent: Optimizing the clipping and localization schedules yields the feasible exponent \(r_{\mathrm{up}}=r_{\mathrm{feas}}\).

@formal def:feasible-rate

- The tuning chooses how aggressively to clip and how tightly to localize near small contrasts.
- In the nonbinding branch, the feasible exponent reaches \(r_\star(\alpha,\gamma)\).
- In the binding branch, the displayed balance gives the procedure’s nuisance-limited exponent.

---

## Conditional upper bound

@informal oeq:feasible-upper: Under the stated policy, cross-fitting, nuisance, boundedness, and localized empirical-process conditions, the clipped AIPW ERM has regret at most \(C n^{-r_{\mathrm{up}}}(\log n)^p\).

@formal oeq:feasible-upper

- The result is conditional on supplied nuisance estimates satisfying the stated rates.
- For \(\gamma=0\), fixed clipping recovers the strict-overlap margin exponent subject to the product nuisance rate.
- For \(\gamma>0\), clipping and localization trade off variance, drift, and nuisance learning.

---

## Open questions

@formal oeq:feasible-tight

- The lower bound supplies the observed-law converse exponent \(r_\star(\alpha,\gamma)\).
- The clipped AIPW analysis supplies the conditional exponent \(r_{\mathrm{up}}\) for one feasible rule.
- The strict-gap branch identifies where weak-arm nuisance learning is the remaining statistical issue.

---

## Conclusion

- We calibrate offline policy-learning regret when weak overlap and small contrasts occur together.
- The lower-bound exponent comes from balancing contrast size, margin mass, and informative-arm probability.
- The clipped cross-fitted AIPW ERM matches that exponent up to logarithms in the nonbinding nuisance-and-clipping regime.
- In the binding regime, the analysis gives the rule’s nuisance-limited exponent and isolates the feasible-tightness question.
