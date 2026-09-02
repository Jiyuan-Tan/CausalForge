# Honest Length for Transported Complier Effects

Under weak transported first stages, honest confidence-set length is governed by \(t_n\), the effective identification strength: source sample size times squared target first stage, deflated by transport-weight dispersion.

---

## The Punchline

- The paper studies a transported LATE-style ratio in a two-sample encouragement design.
- Source data contain covariates, encouragement, receipt, and outcomes.
- Target data contain covariates, so the source experiment is reweighted to the target population.
- The target complier effect is identified as a transported Wald ratio inside \(\Theta=[-1,1]\).
- A confidence set is *honest* when its coverage is at least \(1-\alpha\) uniformly over the whole model class, not merely at one law.
- Fixing a strength threshold \(t_0\), the *frontier* is the worst-case limiting expected length over laws with \(t_n\ge t_0\); it has order \(\min\{1,t_0^{-1/2}\}\).
- Score inversion attains this order, and finite-cell target-weight learning preserves it.

---

## The Question

- Imagine a job-training encouragement experiment run in one source site.
- Some people take up training only when encouraged; these are the compliers.
- The target site has covariates but lacks outcomes, receipt, and encouragement.
- We want the treatment effect for target-site compliers.
- The hard case is a weak transported first stage: few target compliers after reweighting.
- How short can an honest confidence set be?

---

## Why Transport Changes Weak-IV Inference

- In a single source population, first-stage strength scales like sample size times squared compliance share.
- Transport adds uneven target-to-source reweighting.
- A few highly weighted source covariate cells can carry much of the target population.
- The relevant strength is \(t_n=n\mu_n^2/\kappa_n\), where \(\mu_n\) is the transported first-stage mean and \(\kappa_n\) is Kish weight dispersion.
- The next slides define the assumptions that make this scalar the right one.

@figure transported-encouragement-design: Source covariates, encouragement, receipt, and outcomes are reweighted by target covariates to identify a target complier effect.

---

## Data and IV Structure

- The full-data world has source/target status \(S\), covariates \(X\), receipt potentials \(D(0),D(1)\), and outcome potentials \(Y(0),Y(1)\).
- The source population supplies the encouragement experiment.
- The target population supplies the covariate law.
- Outcomes are bounded and receipt is binary, placing complier effects on a compact causal scale.
- Assignment has fixed overlap through \(\varepsilon\), the instrument-overlap constant.
- Randomization, exclusion, and monotonicity give the usual LATE interpretation.

@formal ass:full-data-support

---

## Transport Assumptions

- Outcome transport: the conditional encouragement outcome contrast learned in the source applies at target covariate values.
- Receipt transport: the target-average first-stage contrast is represented by the transported source first stage.
- Target complier positivity gives a positive target complier share.
- Transport domination supplies \(w(X)\), the target-to-source covariate density ratio.
- In the running example, the target site must be represented inside source covariate support.

@formal ass:transport-domination

---

## Dispersion and Weak First Stages

- The weight envelope controls the largest target-to-source density-ratio values at scale \(k_n\).
- The second moment \(\kappa_n\) records how uneven the transport weights are.
- The array lets \(k_n\) grow while keeping \(k_n=o(n^{1/2})\).
- The transported first-stage mean \(\mu_n\) may shrink toward zero.
- These ingredients define \(t_n=n\mu_n^2/\kappa_n\), the effective identification strength.

@formal ass:weight-second-moment

---

## Identification Comes First

@informal prop:compact-causal-range: Under the transported-IV model and integrable source contrasts, the target complier effect equals the transported reduced-form mean divided by the transported first-stage mean and lies in \(\Theta=[-1,1]\).

- The numerator is the transported encouragement effect on outcomes.
- The denominator is the transported encouragement effect on receipt.
- Bounded outcomes and monotone binary receipt make the causal range compact.
- In the job-training example, the target estimand is the outcome gain among target people induced into training by encouragement.

---

## The Key Idea

- Treat each candidate effect \(\vartheta\) as a hypothesis about the transported ratio.
- Subtract \(\vartheta\) times the transported first stage from the transported reduced form.
- Keep \(\vartheta\) when this residual score is small.
- The score radius scales as \(\sqrt{\widehat\kappa_n/n}\).
- Dividing that uncertainty by the first stage yields the length scale \(t_n^{-1/2}\).
- Compactness supplies the order-one scale when effective strength is small.

---

## Where the Literature Stands

- LATE and principal stratification give the complier estimand and IV identification logic.
- Weak-IV robust inference gives Anderson--Rubin and Fieller-style score inversion for ratios.
- Transportability work gives covariate reweighting and target-population interpretation.
- Transported CACE work gives identification and regular estimation under stronger first-stage behavior.
- This paper adds the matched honest expected-length frontier for the bounded transported complier ratio under weak transported first stages.

---

## Oracle Lower Bound

@informal thm:oracle-converse: For every fixed effective-strength threshold \(t_0>0\), oracle honest expected length is at least a constant times \(\min\{1,t_0^{-1/2}\}\) over the transported model and the finite-cell submodel.

@formal thm:oracle-converse

---

## Oracle Score Inversion Attains It

@informal thm:oracle-score-inversion-attainment: With oracle-known transport weights and source propensity, score inversion is honest and has expected length at most a constant times \(\min\{1,t_0^{-1/2}\}\).

@formal thm:oracle-score-inversion-attainment

---

## Why the Novelty Wins

- A direct Wald plug-in ratio becomes unstable when the transported first-stage estimate is close to zero.
- Score inversion tests the reduced-form restriction for each candidate \(\vartheta\), so coverage is tied to a bounded score rather than division by a noisy denominator.
- Transport-weight dispersion enters through \(\widehat\kappa_n\), matching the variance scale of weighted source scores.
- The effective first-stage signal enters through \(\mu_n\), producing \(t_n=n\mu_n^2/\kappa_n\).
- The procedure balances score noise \(\sqrt{\kappa_n/n}\) against transported first-stage slope \(\mu_n\).

@figure score-inversion-pipeline: Candidate values in \(\Theta\) are passed through a transported source score, compared with a dispersion-calibrated radius, and retained as the confidence set.

---

## Fixed Geometry

@informal thm:fixed-geometry-frontier: For every admissible deterministic source-covariate, transport-weight, and propensity geometry, the fixed-geometry minimax expected length is between constants times \(\min\{1,t_0^{-1/2}\}\).

@informal prop:no-shift-reduction: When \(w(X)=1\), the transport dispersion is \(\kappa_n=1\), the target and source covariate laws coincide, and the fixed-geometry frontier is governed by \(n\mu_n^2\).

@formal thm:fixed-geometry-frontier

---

## Learning Weights in Finite Cells

- In the uniform finite-cell design, the target sample estimates target cell masses.
- The source sample estimates cellwise outcome and receipt contrasts.
- A target-sample collision statistic — how often two target draws land in the same cell — estimates the weight-dispersion component.
- The resulting score inversion is sample-only in the finite-cell experiment.
- The regular-cell extension uses known regular source-cell probabilities and known cell-varying propensity.

@informal thm:finite-cell-unknown-weight-attainment: In uniform finite-cell designs with \(k_n\to\infty\) and \(k_n/\sqrt n\to0\), a sample-only score inversion is honest and has expected length at most a constant times \(\min\{1,t_0^{-1/2}\}\), with a matching lower bound.

@informal thm:regular-cell-unknown-weight-attainment: With known regular source-cell probabilities and known cell-varying propensity, regular-cell score inversion is honest and attains expected length at most a constant times \(\min\{1,t_0^{-1/2}\}\), with a matching lower bound.

@formal thm:finite-cell-unknown-weight-attainment

@formal thm:regular-cell-unknown-weight-attainment

---

## Why the Bounds Are True

- At the true \(\theta_T\), the transported residual score has mean zero.
- Bounded outcomes, binary receipt, fixed overlap, and weight second moments control its variance.
- The confidence-set length is the score radius divided by the first-stage slope, clipped to \(\Theta=[-1,1]\).
- The finite-cell proof adds target-frequency error and controls it through the same dispersion scale.
- The lower bound tilts complier outcomes to move \(\theta_T\) by order \(t_0^{-1/2}\).
- Nearby observed-data laws force honest sets to cover separated parameter values often enough.

---

## Takeaways

- The paper identifies the transported target complier effect as a weighted source Wald ratio in a compact causal range.
- The effective strength \(t_n=n\mu_n^2/\kappa_n\) combines weak compliance and transport-weight dispersion.
- Oracle honest confidence sets have minimax expected-length order \(\min\{1,t_0^{-1/2}\}\).
- Score inversion attains the oracle frontier.
- Uniform and regular finite-cell constructions learn target weights while preserving the same order under the stated growth and regularity conditions.
