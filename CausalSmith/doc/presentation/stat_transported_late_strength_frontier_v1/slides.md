# Honest Length for Transported Complier Effects

Under transported IV contrasts and bounded outcomes, honest confidence-set length is governed by one scalar: the effective strength \(t_n\), the source sample size times the squared transported first stage divided by transport-weight dispersion.

---

## The paper characterizes the honest length frontier

- The target estimand is the complier effect in a target population.
- The source sample has encouragement, receipt, outcomes, and covariates.
- The target sample has covariates.
- Transport weights move source IV contrasts to the target covariate distribution.
- Weak first stages are allowed through \(\mu_n\), the transported first-stage mean.
- The minimax expected length is at most and at least a constant times \(\min\{1,t_0^{-1/2}\}\).

@informal thm:oracle-score-inversion-attainment: Oracle score inversion attains expected length at most a constant times \(\min\{1,t_0^{-1/2}\}\) above each fixed effective-strength threshold.

---

## A running example is an encouragement trial transported to a target population

- A program is offered in a randomized source experiment.
- Some encouraged people take up the program, and some do not.
- The target population is described by covariates but lacks outcomes and receipt.
- The target question is the effect for target compliers: people whose receipt would change if encouraged.
- Covariate shift matters because target compliers may live in source covariate regions with uneven representation.

@figure transported-encouragement-design: Box-and-arrow schematic with source covariates, source encouragement, source receipt, and source outcome feeding source IV contrasts; target covariates feeding target weights; source contrasts and target weights feeding the transported complier effect.

---

## Identification is a transported Wald ratio

- The source encouragement contrast identifies covariate-specific reduced-form and first-stage contrasts.
- Outcome transport moves the source outcome contrast to the target covariate law.
- Receipt transport moves the target-average first stage to the same target covariate law.
- Target complier positivity makes the denominator positive.
- Bounded outcomes and monotone binary receipt place the target complier effect in \(\Theta=[-1,1]\).

@formal prop:compact-causal-range

---

## The assumptions have three jobs

- Source IV validity: random assignment within \(X\), exclusion, monotonicity, and instrument overlap.
- Transport validity: outcome contrasts transport conditionally, and the first-stage contrast transports on the target average.
- Covariate support: the target covariate law is represented by a density ratio \(w\) relative to the source covariate law.
- Weak-first-stage geometry: \(\mu_n\), the transported first-stage mean, may shrink.
- Weight geometry: \(\kappa_n\), the second moment of \(w\), records how uneven transport is.

@formal ass:instrument-overlap

---

## The scalar \(t_n\) combines first-stage weakness and covariate shift

- The effective strength is \(t_n=n\mu_n^2/\kappa_n\).
- Larger \(\mu_n\) means a stronger transported first stage.
- Larger \(\kappa_n\) means target weighting uses the source sample less evenly.
- In the running example, a rare target subgroup with large weights lowers effective information even when the source trial is large.
- The talk’s question is: what honest expected length is possible above \(t_n\ge t_0\)?

@formal ass:weight-second-moment

---

## Existing tools cover pieces of the problem

- LATE theory identifies complier effects from randomized encouragement designs.
- Transportability theory explains how source contrasts can target another covariate distribution.
- Weak-IV robust methods invert reduced-form restrictions when the first stage is small.
- Recent transported CACE work gives identification and regular estimation with a first stage bounded away from zero.
- This paper characterizes honest expected length for the transported ratio when the transported first stage degenerates.

---

## The oracle lower bound fixes the target rate

@informal thm:oracle-converse: Every oracle honest procedure has worst-case expected length at least a constant times \(\min\{1,t_0^{-1/2}\}\) above each fixed effective-strength threshold.

@formal thm:oracle-converse

---

## Score inversion reaches the oracle rate

- For a candidate \(\vartheta\), form the transported source score for \(Y-\vartheta D\).
- Keep \(\vartheta\) when the weighted score is small relative to a radius of order \(\sqrt{\widehat\kappa_n/n}\).
- This is the transported analogue of Anderson--Rubin and Fieller inversion.
- The construction stays inside \(\Theta=[-1,1]\), so weak identification produces a bounded fallback set.
- When \(t_0\) grows, the length contracts at the inverse-square-root threshold scale.

@formal thm:oracle-score-inversion-attainment

---

## Fixed geometry gives the same frontier

- Fix the source covariate law, target-to-source weights, and source propensity.
- Let the causal response law vary subject to the transported IV restrictions.
- The same \(\min\{1,t_0^{-1/2}\}\) expected-length order holds uniformly over admissible geometries.
- Thus \(\kappa_n\) absorbs the transport-weight cost rather than leaving geometry-specific rates.

@informal thm:fixed-geometry-frontier: For every admissible deterministic geometry, the fixed-geometry minimax expected length is between constants times \(\min\{1,t_0^{-1/2}\}\).

@formal thm:fixed-geometry-frontier

---

## With no covariate shift, the index reduces to the usual first-stage scale

- When \(w(X)=1\), the target covariate law equals the source covariate law.
- Then \(\kappa_n=1\).
- The effective strength becomes \(n\mu_n^2\).
- The same fixed-geometry frontier applies.
- This specialization shows exactly how transport dispersion extends the single-population weak-first-stage scale.

@informal prop:no-shift-reduction: Under no covariate shift, the fixed-geometry frontier uses \(t_n=n\mu_n^2\) and has the same two-sided \(\min\{1,t_0^{-1/2}\}\) order.

---

## Finite cells make the transport weights learnable

- In the uniform finite-cell design, source cells have mass \(1/k_n\) and assignment is balanced.
- The target sample estimates each target cell probability.
- The source sample estimates each cell’s outcome and receipt encouragement contrast.
- The transported reduced form and first stage are plug-in averages over target empirical cell frequencies.
- A target-sample collision statistic estimates the weight-dispersion scale.

@figure finite-cell-pipeline: Box-and-arrow schematic with target covariate sample feeding empirical cell frequencies, source sample feeding cellwise IV contrasts, both feeding transported reduced-form and first-stage estimates, then feeding score inversion.

---

## Sample-only finite-cell inversion attains the oracle order

@informal thm:finite-cell-unknown-weight-attainment: In the uniform finite-cell class with \(k_n/\sqrt n\to0\), a sample-only score inversion has expected length at most a constant times \(\min\{1,t_0^{-1/2}\}\), and every feasible honest procedure has expected length at least a constant times that order.

@formal thm:finite-cell-unknown-weight-attainment

---

## Regular nonuniform cells retain the same order

- Source cell probabilities may vary within fixed regular bounds.
- The procedure uses known source cell probabilities and a known cell-varying propensity.
- Target empirical cell frequencies still learn the target covariate law.
- The score radius uses a regular-cell dispersion proxy.
- Under the stated growth and overlap conditions, feasible honest length matches the oracle order.

@informal thm:regular-cell-unknown-weight-attainment: In regular finite-cell designs with known source cell probabilities and known propensity, feasible score inversion attains expected length at most a constant times \(\min\{1,t_0^{-1/2}\}\), with a matching lower bound for feasible honest procedures.

@formal thm:regular-cell-unknown-weight-attainment

---

## The lower-bound story is a local complier tilt

- Fix the transport geometry.
- Place compliers in covariate regions in proportion to the transport weight.
- Calibrate the transported first stage so \(t_n\) equals the threshold.
- Tilt only complier outcomes by a local amount.
- The target complier effect moves, while the observed source and target samples remain close enough to force honest sets to cover both possibilities.
- The largest indistinguishable tilt has the same \(t_0^{-1/2}\) scale.

---

## The upper-bound story is score radius divided by first stage

- The score numerator fluctuates on the transported scale \(\sqrt{\kappa_n/n}\).
- The slope in the candidate value is the transported first stage \(\mu_n\).
- Dividing score noise by slope gives \(\sqrt{\kappa_n/(n\mu_n^2)}=t_n^{-1/2}\).
- When this exceeds the diameter of \([-1,1]\), the compact causal range sets the length scale.
- That is the elbow: order one at weak effective strength, inverse-square-root improvement above it.

---

## The contribution is an honest length theory for transported ratios

- The paper identifies the target complier effect as a transported Wald ratio in a compact causal range.
- It shows that \(t_n=n\mu_n^2/\kappa_n\) is the effective-strength index for honest expected length.
- It proves matching lower and upper oracle bounds of order \(\min\{1,t_0^{-1/2}\}\).
- It shows the same order within every admissible fixed transport geometry.
- It constructs finite-cell feasible score inversions that learn target weights and retain the oracle order under the stated regularity conditions.
