# Sharp Rates for Discrete Confounding

For fixed interior overlap, the paper characterizes the minimax MSE for finite-alphabet ATE estimation as \(1/n+d^2/(n^2(\log n)^2)\) and constructs a computable estimator that attains it.

---

## Overview

- The setting is observational ATE estimation with a discrete covariate \(X\in\{1,\ldots,d\}\).
- Each category has unrestricted treatment probabilities and outcome means.
- Fixed overlap keeps both treatment arms present in every positive-mass category.
- The paper establishes the minimax MSE rate for each fixed \(\epsilon\in(0,1/2)\), the overlap parameter.
- The rate separates ordinary sampling error from the price of many unrestricted categories.
- The estimator is explicit: ratios for well-observed categories, polynomial moments for sparse categories.

---

## Discrete adjustment creates a rate question

- A category is a covariate cell, such as an age-by-region-by-risk-profile bin.
- Within each cell, the ATE contribution compares treated and control outcome means.
- With many cells, some denominators are small even when population overlap holds.
- Standard plug-in, IPW, and doubly robust estimators collapse to the same count-based rule in the closest prior model.
- That rule has worst-case MSE scale \(d^2/n^2+1/n\).
- The minimax lower bound from prior work is smaller by a \((\log n)^2\) factor in the large-alphabet term.

---

## The model is deliberately unrestricted across cells

@formal ass:iid-sampling

@formal ass:overlap

- Think of each category as having its own propensity score and two outcome means.
- Fixed overlap means every positive-mass category has treated and untreated units at the population level.
- The hard part is sampling: many population cells may be too small to support stable within-cell ratios.

---

## The target is a sum of cell contrasts

- For category \(k\), the four observed cell masses collect treatment, control, outcome one, and outcome zero probabilities.
- The cell contribution is category mass times treated-minus-control outcome mean.
- The ATE functional \(\tau(P)\) is the sum of these contributions over \(k=1,\ldots,d\).
- Consistency and conditional exchangeability give the usual causal interpretation of this adjusted contrast.
- The decision problem asks for worst-case mean-squared error over all fixed-overlap observed laws.

@formal ass:consistency

@formal ass:conditional-exchangeability

---

## The estimator treats dense and sparse cells differently

@figure hybrid-estimator-pipeline: A box-and-arrow schematic showing the sample split into a pilot half and an estimation half, the pilot half classifying categories as heavy or light, heavy categories flowing to empirical ratio estimates, light categories flowing to Chebyshev factorial-moment estimates, and both branches flowing to a clipped ATE estimate.

- Split the sample in half.
- Use the pilot half to classify categories as heavy or light.
- Heavy means the pilot count exceeds a threshold of order \(\log n\).
- Estimate heavy categories by empirical treatment-control ratios on the second half.
- Estimate light categories by a Chebyshev reciprocal polynomial of degree about \(\log n\).
- Convert polynomial terms into unbiased count estimates using falling-factorial moments.

---

## The central difficulty is the reciprocal

- The category contribution contains ratios: outcome-one mass divided by arm mass.
- Direct ratios behave well only when the relevant category and arm counts are large.
- In light categories, the denominator is the singular part of the problem.
- The polynomial branch approximates the reciprocal contribution on a low-mass scale \(B(n)\) of order \(\log n/n\).
- Factorial moments estimate the polynomial’s monomials from counts without plug-in bias.
- The logarithmic gain comes from replacing unstable sparse-cell ratios by an estimable approximation.

---

## Prior work leaves exactly one gap

- Zeng, Balakrishnan, Han, and Kennedy study the same strong-overlap discrete-covariate benchmark.
- Their standard estimators have worst-case MSE \(O(d^2/n^2+1/n)\).
- Their minimax lower bound has scale \(d^2/(n^2(\log n)^2)+1/n\) for \(d\lesssim n\log n\).
- This paper closes the logarithmic gap: an explicit estimator attains that lower scale under fixed interior overlap.

---

## The fixed-interior minimax rate is sharp

@informal thm:sharp-minimax-fixed-interior: For each fixed \(0<\epsilon<1/2\), when \(n\ge N_\epsilon\) and \(d\le\rho_\epsilon n\log n\), the minimax MSE and the hybrid estimator’s worst-case MSE are both within constants of \(1/n+d^2/(n^2(\log n)^2)\).

@formal thm:sharp-minimax-fixed-interior

---

## The rate changes the benchmark for dimension growth

- In the running cell-adjustment example, \(d\) is the number of unrestricted adjustment cells.
- The parametric \(1/n\) rate holds throughout the theorem’s range when \(d=O(\sqrt n\log n)\).
- Consistency holds exactly along sequences with \(d/(n\log n)\to0\), within the displayed fixed-interior range.
- The standard estimator-class benchmark was \(d/n\to0\).
- The polynomial branch accounts for the extra logarithmic factor.

---

## The same hybrid is calibrated across fixed interior overlaps

@informal thm:overlap-adaptive-universal-hybrid: The hybrid estimator is computable from counts in at most \(K\,d\,M(n)^4\) operations, attains the fixed-overlap upper rate for every fixed \(0<\epsilon<1/2\), and combines with a centered estimator to give the stated near-randomization envelope and endpoint bracket.

@formal thm:overlap-adaptive-universal-hybrid

---

## Near randomization has its own simple estimator

@figure overlap-regime-comparison: A box-and-arrow schematic with fixed interior overlap flowing to the ratio-polynomial hybrid estimator, exact randomization flowing to the centered estimator, and near-randomization flowing to a selector comparing their risk certificates.

- At \(\epsilon=1/2\), treatment is randomized within every positive-mass category.
- The centered estimator averages \(2(2A_i-1)(Y_i-1/2)\).
- Its risk is at most \(1/n+4(1/2-\epsilon)^2\).
- The endpoint minimax risk is bracketed between \(1/(100n)\) and \(1/n\).
- The selected envelope records the better of the sparse-cell scale and the near-randomization scale.

---

## Why the upper bound works

- The pilot split makes the heavy/light decision independent of the estimation noise.
- With high probability, pilot-heavy categories have enough population mass for second-half ratios to be controlled.
- Pilot-light categories have mass at most a constant multiple of \(\log n/n\).
- On that light scale, the Chebyshev reciprocal approximation has bias bounded at the rate needed for the large-alphabet term.
- Factorial-moment identities turn the polynomial into an estimable count statistic.
- Variance and covariance bounds keep the sum over many light cells at the same target scale.

---

## Why the lower bound matches

- The lower bound embeds a hard large-alphabet functional-estimation problem into the ATE model.
- Fixed overlap keeps the embedded laws inside the same causal experiment class.
- Moment-matching makes many sparse-cell alternatives statistically hard to distinguish.
- Their ATE values remain separated at the \(d/(n\log n)\) scale.
- Squared separation gives the \(d^2/(n^2(\log n)^2)\) contribution.
- Ordinary Bernoulli sampling supplies the \(1/n\) contribution.

---

## Also in the paper

@informal lem:light-cell-polynomial: The light-cell polynomial branch is computable and has mean-squared error at most a constant times \(1/n+d^2/(n^2(\log n)^2)\) over its calibrated range.

@informal lem:universal-heavy-cell-rate: The heavy-cell ratio branch has mean-squared error at most a constant times \(1/n+d^2/(n^2(\log n)^2)\) over the fixed-overlap calibrated range.

@informal lem:near-randomization-linear-upper: The centered estimator has risk at most \(1/n+4(1/2-\epsilon)^2\).

@informal lem:randomized-endpoint-minimax: At \(\epsilon=1/2\), the minimax MSE lies between \(1/(100n)\) and \(1/n\).

---

## Takeaways

- For unrestricted discrete confounding under fixed interior overlap, the minimax MSE is \(1/n+d^2/(n^2(\log n)^2)\) up to \(\epsilon\)-dependent constants.
- A computable split-sample hybrid estimator attains the upper bound.
- Heavy categories use ordinary empirical ratios.
- Light categories use Chebyshev approximation and factorial moments.
- The result gives a parametric regime up to \(d=O(\sqrt n\log n)\) and a consistency frontier \(d=o(n\log n)\) within the theorem’s range.
- The endpoint analysis explains how the rate connects to exact randomization.
