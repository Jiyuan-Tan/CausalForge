# Sharp Rates for Discrete Confounding

For fixed interior overlap, we characterize the minimax ATE risk as \(1/n+d^2/(n^2(\log n)^2)\) and construct a count-based hybrid estimator that attains it.

---

## Overview

- The setting is observational ATE estimation with a finite covariate alphabet of size \(d\).
- Each category has its own propensity score and outcome means.
- Fixed overlap keeps every positive-mass category inside \(\epsilon\le\pi_k\le1-\epsilon\).
- The sharp mean-squared-error rate is \(1/n+d^2/(n^2(\log n)^2)\).
- The estimator reaches the lower-bound scale by combining ratios on abundant categories with polynomial estimation on sparse categories.

---

## Motivation

- Discrete covariates are a clean benchmark for high-dimensional adjustment.
- A category can be a covariate profile: age bin, location, diagnosis group, baseline score bin, or their full interaction.
- With many profiles, many categories have few observations even when \(n\) is large.
- Standard cellwise ATE estimators then pay for unstable treatment-control ratios.
- The question is: what is the best possible error when the categorywise nuisance functions are unrestricted?

---

## Related literature

- Rubin (1974) and Rosenbaum and Rubin (1983) organize ATE identification around potential outcomes, exchangeability, and overlap.
- Hahn (1998), Hirano, Imbens, and Ridder (2003), and Robins, Rotnitzky, and Zhao (1994) give the semiparametric ATE benchmark.
- Robins and Ritov (1997) highlight the inferential difficulty created by unrestricted high-dimensional adjustment.
- Jiao et al. (2015), Wu and Yang (2016), and Han et al. (2020) show how polynomial approximation sharpens large-alphabet functional estimation.
- Zeng et al. (2024) give the direct discrete-covariate causal predecessor and the lower-bound scale we attain.

---

## Setup

- We observe \(O_i=(X_i,A_i,Y_i)\) for \(i=1,\ldots,n\).
- \(X\) takes one of \(d\) categories, while \(A\) and \(Y\) are binary.
- \(p_k\) is the category mass, \(\pi_k\) is the treatment probability, and \(\mu_{ak}\) is the outcome mean in arm \(a\).
- The overlap parameter \(\epsilon\) fixes how close category-level assignment can be to deterministic.
- The target is the category-adjusted ATE, written as \(\tau(P)\).

@formal ass:iid-sampling

---

## Causal interpretation

- Consistency links the observed outcome to the potential outcome under the realized treatment.
- Conditional exchangeability says treatment is as good as random after conditioning on the finite category \(X\).
- Fixed overlap gives both treatment arms population support inside every positive-mass category.
- Together, these assumptions make \(\tau(P)\) the finite-alphabet adjusted ATE.

@formal ass:overlap

@formal ass:consistency

@formal ass:conditional-exchangeability

---

## Risk target

- We evaluate worst-case mean-squared error over the overlap-restricted iid experiment class.
- The decision problem lets the distribution vary freely across all category-treatment-outcome cells subject to fixed overlap.
- This isolates the statistical price of unrestricted discrete confounding.

@formal def:minimax-risk

---

## Central insight

- Abundant categories and sparse categories need different estimators.
- Heavy categories have enough observations for empirical treatment-control ratios.
- Light categories have unstable denominators, so direct ratios create the large-alphabet cost seen in plug-in methods.
- We approximate the reciprocal structure in the light-cell contribution by a Chebyshev polynomial of degree about \(\log n\).
- Falling-factorial moments turn that polynomial into an estimable count statistic.
- The logarithmic degree creates the \(d^2/(n^2(\log n)^2)\) large-alphabet term.

---

## Estimator pipeline

@figure hybrid-pipeline: Box-and-arrow schematic showing observed sample split into pilot counts and estimation counts; pilot counts classify categories as heavy or light; heavy categories go to ratio estimation; light categories go to Chebyshev polynomial factorial-moment estimation; both branches are summed and clipped to form the hybrid ATE estimator.

- Split the sample in half.
- Use the pilot split to classify categories as heavy or light at the \(L=\log(en)\) scale.
- Estimate heavy categories by second-split empirical ratios.
- Estimate light categories by a Chebyshev reciprocal polynomial lifted through factorial moments.
- Add the two branches and clip the result to \([-1,1]\).

---

## Light cells

@informal lem:light-cell-polynomial: Under fixed overlap and \(d\le c_\epsilon n\log n\), the light-cell polynomial branch has mean-squared error at most a constant times \(1/n+d^2/(n^2(\log n)^2)\).

- The polynomial branch targets the sparse categories where empirical ratios are most fragile.
- Chebyshev approximation controls the bias of the reciprocal terms.
- Factorial moments estimate each polynomial monomial directly from counts.
- Computation is linear in \(d\) and polynomial in the logarithmic degree \(M(n)\).

---

## Heavy cells

@informal lem:universal-heavy-cell-rate: Under fixed interior overlap and \(d\le\rho_\epsilon n\log n\), the heavy-cell ratio branch has mean-squared error at most a constant times \(1/n+d^2/(n^2(\log n)^2)\).

- The pilot split certifies that heavy categories have population mass at the logarithmic threshold.
- The estimation split then handles treatment-control ratios with controlled denominator events.
- The heavy branch contributes at the same scale as the light branch.

---

## Lower bound

@informal lem:ate-lower-bound-transfer: For every fixed \(0<\epsilon<1/2\), the minimax risk is at least a constant times \(1/n+d^2/(n^2(\log n)^2)\) when \(n\ge N_\epsilon\) and \(d\le b_\epsilon n\log n\).

- Zeng et al. (2024) provide the large-alphabet lower-bound technology for this causal experiment.
- The transfer step places that lower bound inside the fixed-overlap ATE risk.
- The result says the polynomial estimator reaches the correct benchmark.

---

## Main result

@informal thm:sharp-minimax-fixed-interior: For fixed \(0<\epsilon<1/2\), \(n\ge N_\epsilon\), and \(d\le\rho_\epsilon n\log n\), the minimax MSE is bracketed above and below by constants times \(1/n+d^2/(n^2(\log n)^2)\).

@formal thm:sharp-minimax-fixed-interior

---

## Consequences

- The ordinary sampling term is \(1/n\).
- The unrestricted discrete-confounding term is \(d^2/(n^2(\log n)^2)\).
- In the parametric interior, \(d=O(\sqrt n\log n)\) gives risk of order \(1/n\).
- Along sequences in the theorem’s range, consistency is equivalent to \(d/(n\log n)\to0\).
- In the running profile example, adjustment remains consistent across nearly \(n\log n\) unrestricted profiles up to the theorem’s vanishing normalized dimension condition.

---

## Endpoint comparison

@informal thm:overlap-adaptive-universal-hybrid: The same hybrid estimator is computable and attains the fixed-overlap rate, while a centered estimator gives the near-randomization envelope and the exact randomization endpoint has minimax risk between \(1/(100n)\) and \(1/n\).

@formal thm:overlap-adaptive-universal-hybrid

---

## Proof sketch

- First, the pilot split sorts categories with polynomially small classification error.
- Second, light cells use approximation: the Chebyshev reciprocal polynomial keeps sparse-cell bias at the target scale.
- Third, factorial moments estimate the polynomial terms while controlling variance and cross-category covariance.
- Fourth, heavy cells use ratio residual bounds and missing-arm controls.
- Finally, the lower bound and the two upper branches meet at the same fixed-interior rate.

---

## Takeaways

- We characterize the fixed-interior minimax MSE rate for unrestricted finite-alphabet ATE estimation.
- We construct a computable hybrid estimator that attains the rate with universal numerical tuning.
- The rate gives a parametric window \(d=O(\sqrt n\log n)\) and a consistency frontier \(d=o(n\log n)\) within the calibrated theorem range.
- The endpoint results connect the fixed-overlap analysis to exact randomization, where the risk is parametric.
