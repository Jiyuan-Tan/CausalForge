# The Interior Dose-Response Floor

Under fixed interior overlap and Hölder smoothness, estimating the dose-response partial mean at \(t_0\), the evaluation dose, has minimax MSE at least of order \(n^{-2\alpha/(2\alpha+1)}\), for every fixed treatment-density smoothness \(\beta>0\).

---

## The Punchline

- The target is the average outcome if every unit were evaluated at the same interior dose \(t_0\).
- The paper proves a same-class minimax lower bound over the Hölder dose class \(\mathcal P_{\alpha,\beta,s}(M,c_0,\varepsilon_0,t_0)\).
- The lower-bound exponent is the one-dimensional treatment-regression exponent.
- The result holds for every fixed \(\beta>0\), with constants and slack-baseline feasibility calibrated to the fixed model constants.
- In the smooth-covariate regime \(d\le 4s\), this exponent agrees with the published higher-order influence function (HOIF) benchmark \(\rho_n\).
- The talk explains why the hardest subproblem already lives in the treatment coordinate.

---

## The Econometric Question

- Continuous-treatment papers often target a dose-response curve: what would the mean outcome be at dose \(t\)?
- With covariates, the standard adjusted target is a partial mean of the conditional outcome regression.
- Here the focus is one fixed interior dose \(t_0\), away from boundary behavior at 0 and 1.
- Running example: estimate mean health outcome at a clinically relevant drug dose, adjusting for baseline covariates.
- The minimax question is: how small can worst-case squared error be over a smooth nonparametric class?

---

## The Observed-Data Target

- One observation is \(O=(Y,A,X)\): outcome, continuous dose, and covariates.
- The regression \(\mu_P(a,x)\) is the conditional mean of \(Y\) at dose \(a\) and covariates \(x\).
- The treatment density \(\pi_P(a\mid x)\) describes how much data appear near each dose after conditioning.
- The target \(\theta_P(t_0)\) averages \(\mu_P(t_0,X)\) over the covariate distribution.
- Under consistency, no unmeasured confounding, and local positivity, this observed-data partial mean has the usual causal dose-response interpretation.
- In the drug-dose example, \(\theta_P(t_0)\) is the covariate-adjusted mean outcome at dose \(t_0\).

---

## The Model Class in Words

- Outcomes are uniformly bounded by \(M\).
- The evaluation window \([t_0-\varepsilon_0,t_0+\varepsilon_0]\) lies inside the dose support.
- Local positivity keeps the treatment density at least \(c_0\) throughout that window.
- Treatment-direction smoothness: \(a\mapsto\mu_P(a,x)\) is \(\alpha\)-Hölder, and \(a\mapsto\pi_P(a\mid x)\) is \(\beta\)-Hölder.
- Covariate-direction smoothness: \(\mu_P(t_0,x)\), \(\pi_P(t_0\mid x)\), and \(p_{X,P}(x)\) are \(s\)-Hölder in \(x\).
- These restrictions define the same class used for the lower-bound risk.

---

## The Two Load-Bearing Conditions

- Interior overlap means every covariate profile has usable dose variation near \(t_0\).
@formal ass:local-positivity

- Strict baseline slack supplies interior baseline densities \(p_0\) and \(q_0\) with margin \(\eta_0\).
- That margin lets the proof perturb the regression while preserving boundedness, smoothness, and positivity.
- In the drug-dose example, the baseline design has enough untreated slack around the target dose to embed hard local alternatives.

---

## The Key Idea

- The construction freezes the covariate distribution and the treatment density.
- It varies only the treatment regression in a narrow neighborhood of \(t_0\).
- The perturbation has width \(h\) in the dose coordinate and height proportional to the Hölder allowance at that width.
- The two alternatives move the target \(\theta_P(t_0)\) while keeping the sample laws statistically close.
- Because the density is fixed, the obstruction is present for every fixed \(\beta>0\).
@figure lower-bound-pipeline: Two observed-data laws share the same covariate density and treatment density, differ only by a local regression bump around \(t_0\), and induce separated target values.

---

## Where the Literature Stands

- Potential-outcome and generalized propensity-score work gives the causal language for continuous doses.
- Semiparametric and orthogonal-score work explains how nuisance estimation enters partial-mean problems.
- Kennedy and related econometric work study doubly robust continuous-treatment curve estimation.
- Bonvini and Kennedy provide the closest HOIF benchmark rate \(\rho_n\) under additional localized regularity.
- This paper supplies the converse lower-bound side for the interior fixed-dose partial mean over the stated Hölder class.

---

## Main Lower Bound

@informal thm:sharp-pointwise-lower-bound: Under positive smoothness, interior constants, and strict baseline slack, the minimax risk is at least a constant times \(n^{-2\alpha/(2\alpha+1)}\) for every fixed \(\beta>0\).

@formal thm:sharp-pointwise-lower-bound

---

## Why the Bound Is New

- The lower floor is proved on the same Hölder dose class \(\mathcal P_{\alpha,\beta,s}(M,c_0,\varepsilon_0,t_0)\).
- The exponent is governed by treatment-regression smoothness \(\alpha\).
- The treatment-density smoothness \(\beta\) remains part of the class, while the hard alternatives keep the treatment density fixed.
- The proof isolates an unavoidable one-dimensional regression problem inside the causal partial-mean experiment.
- The statistical tradeoff is the usual local-testing balance: target separation squared against \(n\)-sample distinguishability.

---

## Comparison with the HOIF Benchmark

- The published benchmark is \(\rho_n=n^{-2\alpha/(2\alpha+1)}\vee n^{-2/(1+d/(4s)+1/\alpha)}\).
- The first term is the treatment-regression scale.
- The second term reflects the covariate-smoothness component in the published HOIF comparison.
- The algebra splits into \(d\le 4s\) and \(4s<d\).

@informal prop:oracle-regime-reduction: When \(d\le 4s\), under the same interior constants and strict-slack baseline, the published benchmark equals the treatment-regression rate, and the same-class minimax risk is at least a constant times \(\rho_n\).

---

## Smooth-Covariate Regime

@informal thm:sharp-minimax-smooth-covariate: When \(d\le 4s\), under the same interior constants and strict-slack baseline, the same-class minimax risk is at least a constant times \(n^{-2\alpha/(2\alpha+1)}\), and this rate equals \(\rho_n\).

@formal thm:sharp-minimax-smooth-covariate

---

## Low-Covariate-Smoothness Regime

@informal thm:frontier-bracket-deficient: When \(4s<d\), under the same interior constants and strict-slack baseline, the same-class minimax risk is still at least a constant times \(n^{-2\alpha/(2\alpha+1)}\), while the published benchmark is governed by \(n^{-2/(1+d/(4s)+1/\alpha)}\) with a strictly smaller exponent.

@formal thm:frontier-bracket-deficient

---

## Also in the Paper

@informal lem:published-upper-bound-cited: Cited, not proved here: under the Bonvini--Kennedy conditions and tuning, the specified HOIF estimator, with its trained nuisances held fixed, attains conditional mean-squared error at most a constant times \(\rho_n\).

@informal def:beta-frontier-handle: The beta comparison handle records the all-\(\beta\) lower floor, the two algebraic benchmark regimes, and the stated same-class upper-frontier alternatives.

---

## Why the Lower Bound Works

- Start with an interior baseline law satisfying the slack condition.
- Add a small regression bump centered at \(t_0\), leaving the covariate density and treatment density unchanged.
- Choose the bump width so the \(\alpha\)-Hölder restriction allows enough height while the sample distributions stay close.
- The target changes because \(\theta_P(t_0)\) reads the regression exactly at the evaluation dose.
- Le Cam’s two-point argument turns close sample laws and separated targets into a minimax MSE floor.

---

## What to Remember

- The paper establishes a same-class lower bound for the interior continuous-treatment dose-response partial mean.
- The certified exponent is \(2\alpha/(2\alpha+1)\), the treatment-regression exponent.
- The conclusion applies for every fixed \(\beta>0\) under the stated slack-baseline condition.
- In the smooth-covariate regime \(d\le 4s\), the lower-bound exponent agrees with the published HOIF benchmark.
- In the \(4s<d\) regime, the paper gives the exact algebraic ordering between the certified lower floor and the published benchmark exponent.
