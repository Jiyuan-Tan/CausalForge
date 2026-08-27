# Sharp Rates for ATEs with Many Discrete Confounders

For fixed interior overlap, and in the calibrated range \(n\ge N_\epsilon\), \(d\le\rho_\epsilon n\log n\), a computable ratio-polynomial hybrid estimator attains the sharp minimax MSE scale \(1/n+d^2/(n^2(\log n)^2)\), expanding the parametric and consistency regimes beyond standard plug-in behavior.

---

## Punchline First

- The problem is ATE estimation with \(d\) unrestricted discrete covariate categories.
- The paper characterizes the fixed-interior minimax risk under overlap level \(\epsilon\in(0,1/2)\).
- The sharp rate is \(1/n+d^2/(n^2(\log n)^2)\) for \(n\ge N_\epsilon\) and \(d\le\rho_\epsilon n\log n\).
- A computable hybrid estimator attains the upper bound with fixed numerical tuning.
- The logarithmic gain moves the parametric window to \(d=O(\sqrt n\log n)\) and the consistency frontier to \(d=o(n\log n)\).
- Near exact randomization, a centered estimator gives a separate envelope and the endpoint risk is parametric.

---

## Why This Question Matters

- In observational studies, adjustment often means comparing treated and control outcomes within covariate strata.
- With many discrete covariate categories, some strata are sparse even when population overlap is bounded.
- Standard cellwise estimators use empirical treatment-control ratios, so sparse denominators create worst-case bias.
- The econometric question is: how much does unrestricted discrete confounding cost in minimax MSE?
- The paper answers this question for fixed interior overlap.

---

## A Two-Category Warning Example

- Take two equally likely covariate categories.
- Treatment is rare in category 1 and common in category 2 when \(\epsilon\) is small.
- Treated potential outcomes differ across categories, while control potential outcomes are zero.
- The causal ATE is a covariate-adjusted object, not the raw treated-control contrast.
- This example motivates adjustment before the high-dimensional rate question.

@formal prop:two-category-confounding

---

## Setup: The Observed Experiment

- One observation is \(O=(X,A,Y)\).
- \(X\) is a covariate category in \(\{1,\ldots,d\}\).
- \(A\) is binary treatment and \(Y\) is a binary outcome.
- Each category has mass \(p_k\), propensity \(\pi_k\), and conditional means \(\mu_{0k},\mu_{1k}\).
- The risk is worst-case over all such finite-alphabet laws satisfying overlap.

@formal ass:iid-sampling

---

## Overlap and Causal Interpretation

- Fixed overlap means every positive-mass category has both treatment arms available in population.
- Interior means the overlap level is strictly inside, \(\epsilon\in(0,1/2)\); the endpoint \(\epsilon=1/2\) is exact randomization and is treated separately.
- In the running example, \(\epsilon\) controls how imbalanced treatment can be across the two categories.
- Consistency and conditional exchangeability give the observed-data functional its ATE interpretation.
- The minimax problem is then about estimating this adjusted target uniformly over unrestricted category laws.

@formal ass:overlap

@formal ass:consistency

@formal ass:conditional-exchangeability

---

## Target and Risk in Plain Language

- The ATE is the sum over categories of: category mass times treated-minus-control mean.
- The hard part is the categorywise ratio structure inside sparse cells.
- The minimax risk \(\mathsf R_{n,d,\epsilon}\) asks for the best worst-case MSE over the overlap-restricted experiment class.
- The paper studies how \(\mathsf R_{n,d,\epsilon}\) changes as \(d\) grows with \(n\).

@figure estimator-target: The diagram shows covariate categories feeding into categorywise treated-minus-control contrasts, then summing into the ATE target \(\tau(P)\).

---

## Key Idea: Treat Heavy and Light Categories Differently

- Heavy categories are pilot-certified by counts above a logarithmic threshold.
- On heavy categories, empirical treatment-control ratios are stable enough.
- Light categories are too sparse for direct ratios.
- On light categories, the estimator replaces the reciprocal ratio by a Chebyshev polynomial of degree \(M(n)\) about \(\log n\).
- Factorial moments turn each polynomial monomial into an estimable count statistic.
- The final estimator adds heavy and light contributions and clips to the natural ATE range.

@figure hybrid-pipeline: The diagram shows a split sample, pilot heavy-light classification, ratio estimation for heavy categories, polynomial factorial-moment estimation for light categories, and aggregation into \(\widehat\tau_n^{\mathrm{hyb}}\).

---

## Where the Literature Stood

- Classical ATE theory gives efficiency results under regular low-dimensional structure.
- High-dimensional causal methods use nuisance structure such as sparsity, smoothness, or orthogonality.
- Large-alphabet functional estimation shows how polynomial approximation can sharpen nonsmooth rates.
- Zeng, Balakrishnan, Han, and Kennedy give the direct discrete-covariate benchmark.
- Their standard plug-in, IPW, and doubly robust estimators have worst-case scale \(d^2/n^2+1/n\).
- Their minimax lower bound has scale \(d^2/(n^2\log^2 n)+1/n\), and this paper attains that lower scale in the fixed-interior regime.

---

## Main Result: The Sharp Fixed-Interior Rate

@informal thm:sharp-minimax-fixed-interior: For each fixed \(\epsilon\in(0,1/2)\), within \(n\ge N_\epsilon\) and \(d\le\rho_\epsilon n\log n\), the minimax MSE and the hybrid estimator’s worst-case MSE are both bounded above and below by constants times \(1/n+d^2/(n^2(\log n)^2)\).

@formal thm:sharp-minimax-fixed-interior

---

## What the Rate Means

- The first term, \(1/n\), is the ordinary sampling cost.
- The second term, \(d^2/(n^2(\log n)^2)\), is the cost of unrestricted discrete confounding.
- In the two-category example, \(d\) is fixed, so the theorem lands in the parametric regime.
- With growing \(d\), the same theorem allows parametric risk through \(d=O(\sqrt n\log n)\).
- Consistency holds exactly along sequences with \(d/(n\log n)\to0\), within the theorem’s displayed dimension range.

---

## The Computable Hybrid and Endpoint Envelope

@informal thm:overlap-adaptive-universal-hybrid: The same count-based hybrid estimator is computable in at most \(K\,d\,M(n)^4\) operations, attains the fixed-overlap upper rate, and combines with a centered estimator to give an upper envelope near exact randomization.

@formal thm:overlap-adaptive-universal-hybrid

---

## Why the Novelty Wins

- The naive plug-in route estimates a reciprocal from sparse arm counts.
- Its large-alphabet term sits at the \(d^2/n^2\) scale in the direct discrete benchmark.
- The hybrid keeps ratios only where pilot counts certify enough mass.
- On light categories, polynomial approximation replaces unstable reciprocals with degree \(M(n)\) about \(\log n\).
- Factorial moments estimate the polynomial terms directly from counts.
- This is the source of the improvement to \(d^2/(n^2(\log n)^2)\).

---

## Why It Is True: Heavy Categories

- The first split identifies categories whose population masses are large enough, up to high-probability sandwich bounds.
- Conditional on that pilot classification, the second split estimates heavy-cell contrasts independently.
- Population overlap turns category mass into enough expected treated and control observations.
- Missing-arm events and ratio residuals are controlled in aggregate.
- The heavy branch contributes within the same \(1/n+d^2/(n^2(\log n)^2)\) envelope.

---

## Why It Is True: Light Categories

- Light categories have small population mass after the pilot sandwich.
- The cell contribution is homogeneous but has reciprocal terms at zero.
- A Chebyshev reciprocal polynomial approximates the contribution on the light-cell mass scale \(B(n)\).
- Falling-factorial moments make the polynomial terms unbiased for their population monomials.
- The degree around \(\log n\) balances approximation error against factorial-moment variance.
- Summing across light categories preserves the target rate.

---

## Why It Is True: The Lower Bound and Endpoint

- The lower bound transfers the large-alphabet discrete functional difficulty into the ATE cell functional.
- The construction creates many hard-to-distinguish sparse category laws with separated ATE values.
- Their statistical distance remains small at the sample size \(n\).
- This gives the matching lower scale in the fixed-interior range.
- At exact randomization, the centered contrast has parametric risk and a one-category Bernoulli argument gives the matching lower bracket.

---

## Takeaways

- The paper establishes the sharp fixed-interior minimax MSE rate \(1/n+d^2/(n^2(\log n)^2)\).
- The constructive upper bound is attained by a computable split-sample ratio-polynomial hybrid estimator.
- The result gives parametric risk through \(d=O(\sqrt n\log n)\) and consistency exactly when \(d=o(n\log n)\) within the calibrated range.
- The endpoint analysis brackets exact randomization at the parametric scale.
- An open direction is the full transition theory for triangular arrays with \(\epsilon=\epsilon_n\) approaching \(1/2\).
