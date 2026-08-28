# Interior Dose-Response Lower Bounds

Under Hölder smoothness, local positivity, bounded outcomes, and strict baseline slack, the minimax mean-squared error for an interior continuous-treatment dose-response partial mean is at least the one-dimensional treatment-regression rate.

---

## Overview

- We study the target-dose partial mean for a continuous treatment.
- The target asks: what is the average outcome if the dose is fixed at an interior value \(t_0\)?
- The lower bound is over the same Hölder dose class used in the risk statement.
- The obstruction comes from learning the outcome regression locally in the treatment coordinate.
- The lower-bound exponent is independent of the treatment-density smoothness \(\beta\), for each fixed \(\beta>0\).

@informal thm:sharp-pointwise-lower-bound: Under the stated smoothness, positivity, boundedness, and strict-slack conditions, the minimax MSE is at least a constant times \(n^{-2\alpha/(2\alpha+1)}\).

---

## Motivation

- Continuous-treatment dose-response curves are common in policy, medicine, and economics.
- A policymaker may ask for the mean outcome at a particular interior dose, rather than for a binary treatment contrast.
- Regression adjustment estimates the conditional mean at that dose and averages over the covariate distribution.
- The hard part is local: observations near \(t_0\) carry the information about the regression value at \(t_0\).
- The minimax question asks how small the worst-case squared error can be.

---

## Running example

- Think of \(A\) as dose intensity, \(Y\) as an outcome, and \(X\) as pre-treatment covariates.
- We evaluate an interior dose \(t_0\), such as a moderate policy intensity or medication level.
- Local positivity says each covariate group has enough probability of receiving doses near \(t_0\).
- Hölder smoothness says the regression and density vary regularly near that dose.
- The target averages the dose-\(t_0\) regression over the population distribution of \(X\).

---

## Target

- One observation is \(O=(Y,A,X)\).
- \(A\) is a continuous treatment in \([0,1]\).
- \(\mu_P(a,x)\) is the conditional mean of \(Y\) at dose \(a\) and covariates \(x\).
- \(p_{X,P}\) is the covariate density.
- The estimand is
\[
\theta_P(t_0)
=
\int_{[0,1]^d} \mu_P(t_0,x)\,p_{X,P}(x)\,dx .
\]

@figure observed-target-pipeline: Box-and-arrow schematic from observed data to the regression, target dose, covariate averaging, target mean, and causal dose-response interpretation under consistency, no confounding, and local positivity.

---

## Identification

- The statistical target is an observed-data partial mean.
- With consistency, the observed outcome equals the potential outcome at the realized dose.
- With no unmeasured confounding, treatment assignment is conditionally independent of potential outcomes given \(X\).
- With local positivity, the data contain information near the target dose for every covariate value.
- These conditions give the causal reading of \(\theta_P(t_0)\) as the dose-response mean at \(t_0\).

---

## Model

- Outcomes are uniformly bounded by \(M\).
- The dose \(t_0\) has a full local window inside \((0,1)\).
- The treatment density is bounded below by \(c_0\) on that window.
- The treatment regression has Hölder smoothness \(\alpha\) in the dose coordinate.
- The treatment density has Hölder smoothness \(\beta\) in the dose coordinate.
- The regression, treatment density, and covariate density have Hölder smoothness \(s\) in the covariate coordinate.

---

## Baseline slack

- The lower-bound construction starts from baseline densities \(p_0\) and \(q_0\).
- Strict slack means these baselines sit inside the smoothness, boundedness, and positivity restrictions with positive margin.
- That margin lets us add a local perturbation while staying in the same model class.
- In the running example, the baseline population and dose assignment mechanism are regular enough that a small local regression change remains admissible.

@formal ass:baseline-submodel-slack

---

## Related literature

- Rubin (1974), Rosenbaum and Rubin (1983), and Robins (1986) provide the causal potential-outcome and adjustment foundations.
- Imbens (2000), Hirano and Imbens (2004), and Imai and van Dyk (2004) develop continuous-treatment propensity and dose-response ideas.
- Kennedy et al. (2017), Lee (2018), and Colangelo and Lee (2020) study nonparametric and debiased continuous-treatment estimation.
- Bonvini and Kennedy (2022) give the higher-order influence-function benchmark used for comparison.
- Stone (1982) and Tsybakov (2009) provide the nonparametric minimax lower-bound toolkit.

---

## Main result I

@informal thm:sharp-pointwise-lower-bound: For every fixed positive \(\beta\), the same-class minimax MSE is at least a constant times the one-dimensional treatment-regression rate under the stated slack-baseline conditions.

@formal thm:sharp-pointwise-lower-bound

---

## Key idea

- Hold the covariate density and treatment density fixed.
- Perturb only the outcome regression in a narrow neighborhood of \(t_0\).
- The perturbation changes \(\theta_P(t_0)\) because the target evaluates the regression exactly at \(t_0\).
- The induced data laws remain statistically close because the perturbed region is narrow.
- The best test between the two laws cannot reliably detect the target shift.

@figure lower-bound-pipeline: Box-and-arrow schematic showing fixed covariate and treatment densities, a local bump near \(t_0\), two observed-data laws, statistical closeness, target separation, and the resulting all-\(\beta\) lower-bound obstruction.

---

## Intuition

- A direct plug-in view says the problem is to learn \(\mu_P(t_0,x)\) from observations with doses near \(t_0\).
- A very narrow neighborhood gives low bias but few effective observations.
- A wider neighborhood gives more observations but cannot resolve \(\alpha\)-Hölder local variation at \(t_0\).
- The lower-bound construction chooses the local bump width that balances these two forces.
- Because the treatment density is fixed inside the construction, \(\beta\)-smoothness remains part of the class while the hard pair is governed by \(\alpha\).

---

## Smooth covariates

- The published benchmark rate is
\[
\rho_n
=
n^{-2\alpha/(2\alpha+1)}
\vee
n^{-2/(1+d/(4s)+1/\alpha)} .
\]
- When \(d\le 4s\), the benchmark collapses to the treatment-regression term.
- In that regime, the same-class lower floor has the same exponent as \(\rho_n\).

@informal prop:oracle-regime-reduction: In the smooth-covariate regime \(d\le 4s\), the published benchmark equals the treatment-regression rate, and the minimax risk is at least a constant times that benchmark.

---

## Main result II

@informal thm:sharp-minimax-smooth-covariate: When \(d\le 4s\), the same-class lower bound is at least a constant times \(n^{-2\alpha/(2\alpha+1)}\), and this rate equals \(\rho_n\).

@formal thm:sharp-minimax-smooth-covariate

---

## Low covariate smoothness

- When \(4s<d\), the published benchmark is governed by the covariate-smoothness term.
- The lower-bound construction still gives the treatment-regression floor.
- The two exponents are strictly ordered in this regime.
- The result identifies the algebraic gap between the same-class lower floor and the published benchmark sequence.

@informal thm:frontier-bracket-deficient: When \(4s<d\), the minimax risk is still at least the treatment-regression lower floor, while the published benchmark has a strictly smaller exponent.

@formal thm:frontier-bracket-deficient

- This separates the certified same-class lower floor from the published benchmark exponent in the low-covariate-smoothness regime.
- The comparison is exact at the level of the displayed benchmark algebra.

---

## Also in the paper

@informal lem:published-upper-bound-cited: Under the stated Bonvini-Kennedy localized-regularity conditions, the cited higher-order influence-function estimator attains conditional mean-squared error at most a constant times \(\rho_n\).

@informal def:beta-frontier-handle: The beta comparison handle records the all-\(\beta\) lower floor, the two benchmark regimes, and the possible same-class upper-frontier alternatives.

---

## Proof sketch

- Build two laws with the same covariate density and the same treatment density.
- Add a local Hölder-compatible regression bump near \(t_0\) under one law.
- Use bounded two-point outcome channels so the target shift is carried by the conditional mean.
- Calibrate the bump so the \(n\)-sample laws have bounded Kullback-Leibler divergence.
- Apply Le Cam’s two-point argument to convert indistinguishability into a squared-error lower bound.

---

## Takeaways

- The interior dose-response partial mean has a same-class minimax lower floor at \(n^{-2\alpha/(2\alpha+1)}\).
- The floor holds for every fixed \(\beta>0\) under the corresponding strict-slack baseline condition.
- When \(d\le 4s\), this exponent matches the published higher-order influence-function benchmark exponent.
- When \(4s<d\), the benchmark exponent and the certified same-class lower-bound exponent are strictly ordered.
- The comparison clarifies exactly which rate facts are established for the Hölder dose class and which upper-side questions remain for the low-\(s\) regime.
