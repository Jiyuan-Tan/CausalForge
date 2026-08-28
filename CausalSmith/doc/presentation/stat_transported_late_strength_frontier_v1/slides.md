# Honest Length for Transported Complier Effects

Under bounded outcomes and transported IV contrasts, we identify the target complier effect and show that honest confidence-set length is governed by the effective strength \(t_n=n\mu_n^2/\kappa_n\).

---

## Overview

- We study an encouragement design observed in a source population.
- The target population supplies covariates, so effects are transported by reweighting source contrasts.
- The target estimand is the complier effect in the target population.
- Weak first stages make the transported Wald ratio hard to estimate.
- The exact difficulty is summarized by \(t_n\), the effective identification strength.
- Score inversion attains the honest expected-length frontier.

---

## Motivation

- Think of a canvassing or program-offer experiment run in one population.
- In the source, we observe encouragement \(Z\), receipt \(D\), outcome \(Y\), and covariates \(X\).
- In the target, we observe the covariate distribution where we want the complier effect.
- Transport weights can be uneven when the target overrepresents covariate cells that are rare in the source.
- A weak transported first stage and uneven transport weights both reduce usable information.
- The question is: what honest confidence-set length is achievable?

@figure transported-encouragement-design: Box-and-arrow schematic showing source cells and target cells forming transport weights, weighted cells, transported moments, Kish dispersion, effective IV strength, and the target complier effect.

---

## Background

- LATE uses an encouragement-induced outcome contrast divided by an encouragement-induced receipt contrast.
- Imbens and Angrist (1994) and Angrist et al. (1996) give the source IV logic.
- Chen and Huang (2025) study transported complier effects with regular first stages.
- Anderson and Rubin (1949) and Fieller (1954) give the ratio-inference logic used for weak denominators.
- Our contribution combines transport, weak first stages, and honest expected length for a bounded causal ratio.

---

## Setup

- Source population \(S=1\): \(X,Z,D,Y\) are observed.
- Target population \(S=0\): target covariates \(X\) determine the population being transported to.
- Outcomes are bounded in \([0,1]\), and receipt is binary.
- The source encouragement satisfies overlap, randomization, exclusion, and monotonicity.
- Transport uses the target-to-source density ratio \(w(X)\).
- The target complier effect is \(\theta_T\), the target complier-conditional outcome contrast.

---

## Transport assumptions

- Outcome transport: the source conditional assignment-outcome contrast carries to the target at the same \(X\).
- Receipt transport: the target-average receipt contrast equals the target average of the source conditional receipt contrast.
- Target complier positivity gives a positive target complier share.
- Transport domination \(P_T\ll P_S^X\) gives the density ratio \(w=dP_T/dP_S^X\).
- Fixed instrument overlap controls the inverse-propensity source score.
- Kish dispersion \(\kappa_n\) measures how uneven the target-to-source weights are.

---

## Identification

@informal prop:compact-causal-range: Under the transported IV model, the target complier effect equals the transported Wald ratio and lies in \(\Theta=[-1,1]\).

@formal prop:compact-causal-range

---

## Effective strength

- The transported first-stage mean is \(\mu_n\), the target average compliance contrast.
- The weight-dispersion scale is \(\kappa_n=\mathbb E_S[w(X)^2]\).
- The effective identification strength is
\[
t_n=\frac{n\mu_n^2}{\kappa_n}.
\]
- Larger \(\mu_n\) strengthens the denominator.
- Larger \(\kappa_n\) reduces the effective source information.
- The expected-length frontier is indexed by a fixed threshold \(t_0\).

---

## Score inversion

- For each candidate \(\vartheta\in\Theta\), form a transported source score for \(Y-\vartheta D\).
- Keep candidate values whose score is small relative to the weight-dispersion radius.
- This is the transported Anderson-Rubin and Fieller logic.
- The compact range \(\Theta=[-1,1]\) keeps the ratio inference on the causal outcome scale.

@figure score-inversion-pipeline: Box-and-arrow schematic showing candidate values, empirical first stage, transported source score, weight dispersion, critical radius, comparison, and retained confidence set.

---

## Oracle frontier

@informal thm:oracle-converse: Any oracle honest procedure has worst-case expected length at least a constant multiple of \(\min\{1,t_0^{-1/2}\}\) above effective strength \(t_0\).

@formal thm:oracle-converse

@informal thm:oracle-score-inversion-attainment: Oracle score inversion is honest and has worst-case expected length at most a constant multiple of \(\min\{1,t_0^{-1/2}\}\).

@formal thm:oracle-score-inversion-attainment

---

## Fixed geometry

- Fix the source covariate law, transport weights, and source propensity.
- Let the causal response law vary within the transported IV model.
- The same effective-strength frontier holds uniformly over admissible deterministic geometries.
- This shows that \(t_n\) absorbs both first-stage weakness and transport dispersion.
- With no covariate shift, \(w(X)=1\), \(\kappa_n=1\), and \(t_n=n\mu_n^2\).

@informal thm:fixed-geometry-frontier: For every admissible fixed geometry, the minimax expected length is bounded above and below by constants times \(\min\{1,t_0^{-1/2}\}\).

@formal thm:fixed-geometry-frontier

@informal prop:no-shift-reduction: With unit transport weights, the fixed-geometry frontier has the same \(\min\{1,t_0^{-1/2}\}\) order with \(t_n=n\mu_n^2\).

---

## Cell weight learning

- In the uniform finite-cell design, target covariates identify target cell frequencies.
- Source data estimate outcome and receipt contrasts within each cell.
- The transported reduced form and first stage average those cell contrasts using empirical target frequencies.
- A target-sample collision statistic estimates the weight-dispersion scale.
- The resulting score inversion uses observed samples only.

@figure finite-cell-pipeline: Box-and-arrow schematic showing target cell labels, empirical cell frequencies, collision statistic, source outcome-receipt-encouragement data, cellwise IV contrasts, transported estimates, and score inversion.

---

## Finite-cell result

@informal thm:finite-cell-unknown-weight-attainment: In the uniform finite-cell class with \(k_n/\sqrt n\to0\), a sample-only score inversion attains expected length at most a constant multiple of \(\min\{1,t_0^{-1/2}\}\), with a matching lower bound.

@formal thm:finite-cell-unknown-weight-attainment

---

## Regular cells

- The regular extension allows source cell probabilities to vary within fixed constants times \(1/k_n\).
- The construction uses known source cell probabilities and a known cell-varying propensity.
- Empirical target frequencies still supply the transported target weights.
- The same strength-indexed expected-length order is attained.

@informal thm:regular-cell-unknown-weight-attainment: With known regular source-cell probabilities and known propensity, feasible regular-cell score inversion attains the oracle frontier order on \(\mathcal N_n^{\mathrm{reg}}\).

@formal thm:regular-cell-unknown-weight-attainment

---

## Proof sketch

- The upper bound starts from score inversion over the compact causal range.
- At the true \(\theta_T\), the transported score is centered.
- Bounded outcomes, binary receipt, overlap, and weight dispersion control the score radius.
- When the empirical first stage is stable, score inversion has length on the order of radius divided by the first stage.
- The bad-slope probability is controlled by the same effective strength \(t_n\).
- The compact range supplies the order-one length scale at weak effective strength.

---

## Lower-bound idea

- Fix an admissible transport geometry.
- Calibrate complier probabilities proportional to the transport weights.
- This makes the transported first stage match the threshold \(t_0\).
- Tilt only the complier outcome mean.
- The tilt moves \(\theta_T\) while the observed-data laws remain close.
- Honesty therefore forces confidence sets to cover separated target complier effects with nontrivial probability.

---

## Conclusion

- We identify \(\theta_T\) as a transported complier ratio in the compact range \([-1,1]\).
- We characterize honest expected length through \(t_n=n\mu_n^2/\kappa_n\).
- Oracle score inversion attains the minimax order \(\min\{1,t_0^{-1/2}\}\).
- The same order holds at fixed transport geometry.
- Finite-cell target-weight learning preserves the oracle frontier under the stated growth and regularity conditions.
