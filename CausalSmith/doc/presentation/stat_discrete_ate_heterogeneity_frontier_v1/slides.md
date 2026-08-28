# Minimax ATE Estimation With Many Discrete Cells

With fixed overlap and a known heterogeneity radius, we give finite-sample minimax benchmarks for average treatment effect estimation and construct clipped estimators that match the lower benchmark in the main regimes.

---

## Overview

- Target: scalar average treatment effect with a finite discrete adjustment variable.
- Challenge: many cells may be sparsely populated and unevenly weighted.
- Organizing parameter: \(\sigma\), the heterogeneity radius for cell treatment effects.
- Main output: a finite-sample minimax bracket indexed by \(n,d,M,\sigma\).
- Constructive side: a known-radius selector over polynomial, collision, and zero branches.
- Converse side: binary hard experiments transported into the same real-outcome class.

@informal thm:two-sided-minimax-bracket-all-d: Under fixed overlap, bounded outcome scale, and radius \(0\le\sigma\le2\), the minimax mean-squared risk lies between the stated lower benchmark and at most the stated selector benchmark.

---

## Motivation

- Think of adjustment cells as age-by-income-by-region-by-baseline-history groups.
- Identification says we should compare treated and control outcomes within each cell.
- Finite samples create a second problem: some cells contain treated observations, controls, or neither.
- When \(d\) is large, the obstacle is combinatorial as much as statistical.
- The estimand is still one scalar ATE, but the data arrive through many sparse cells.

---

## Research question

- Suppose treatment is ignorable within a finite cell \(X\in\{1,\ldots,d\}\).
- Suppose every supported cell has fixed overlap \(\epsilon\le\pi_k\le1-\epsilon\).
- Suppose outcomes are real-valued, centered on scale \(M\), with conditional second moments at most \(M^2\).
- Suppose cell effects differ from the ATE by at most \(\sigma M\).
- What is the best finite-sample mean-squared error as \(n,d,\sigma\) vary?

---

## Setup

- \(p_k\) is the cell mass \(P(X=k)\).
- \(\pi_k\) is the cell propensity \(P(A=1\mid X=k)\).
- \(\mu_{ak}\) is the conditional mean outcome in arm \(a\) and cell \(k\).
- \(\tau_k=\mu_{1k}-\mu_{0k}\) is the cell treatment effect.
- \(\tau(P)=\sum_k p_k\tau_k\) is the average treatment effect.
- \(\delta_k=\tau_k-\tau(P)\) is the cell-effect deviation.

@formal def:ate-functional

---

## Assumptions

- Consistency and conditional exchangeability give the observed-data causal interpretation.
- Fixed overlap keeps both treatment arms available in every supported cell.
- Mean normalization fixes the outcome scale \(M\).
- The second-central-moment bound allows real outcomes with variance control.
- Approximate homogeneity says the largest supported-cell deviation is at most \(\sigma M\).

@formal ass:overlap

@formal ass:approximate-homogeneity

---

## Model class

- We work on one radius-indexed real-outcome model class.
- The class allows arbitrary cell masses.
- The radius \(\sigma\in[0,2]\) moves from exact homogeneity to unrestricted heterogeneity on the normalized scale.
- The minimax criterion asks for worst-case squared error over this class.

@formal def:model-class

@formal def:minimax-risk

---

## Related literature

- Rubin (1974), Rubin (1979), and Rosenbaum and Rubin (1983) supply the potential-outcomes adjustment logic.
- Hahn (1998) and Hirano et al. (2003) give classical efficiency benchmarks for ATE estimation.
- Belloni et al. (2017), Chernozhukov et al. (2018), and Kennedy (2022) study high-dimensional nuisance estimation.
- Wager and Athey (2018), Nie and Wager (2021), and Semenova and Chernozhukov (2021) focus on heterogeneous-effect learning.
- Zeng et al. (2024) identify the closest sparse discrete-adjustment collision phenomena for binary outcomes.
- Jiao et al. (2015) and Wu and Yang (2016) supply the large-alphabet polynomial-estimation toolkit.

---

## Key idea

- Sparse cells create two useful regimes.
- Rare-cell regime: estimate a large-alphabet functional with a polynomial approximation.
- Crossed-cell regime: use cells where both treatment arms appear and borrow through the homogeneity radius.
- The known radius \(\sigma\) tells us which branch has the better benchmark.
- The zero branch handles fully saturated scales through clipping.

@figure estimator-pipeline: Box-and-arrow schematic showing observed data flowing into heavy-light classification, polynomial estimation, collision estimation, zero estimation, and a known-radius selector.

---

## Estimators

- Heavy cells: use plug-in treated-control contrasts on the estimation split.
- Light cells: use a signed Chebyshev factorial device at degree \(K_n\).
- Crossed cells: average treated-control contrasts over cells where both arms are observed.
- Selector: compare \(u_{n,d}=d^2/[n^2\log^2(en)]\), \(h_{n,d,\sigma}=\sigma^2+d/n^2\), and \(1\).
- All branches are clipped to \([-M,M]\).

@informal thm:robust-upper-construction-resolution-all-d: The polynomial branch has risk at most the parametric term plus the rare-cell polynomial remainder, and the collision branch has risk at most the parametric term plus \(\sigma^2+d/n^2\).

@formal def:total-estimator

---

## Upper bound

- The selector inherits the better available branch.
- Polynomial estimation pays the rare-cell scale.
- Collision estimation pays the heterogeneity radius and the crossed-cell occupancy scale.
- The constant-zero branch protects the all-alphabet statement — validity at every alphabet size \(d\), not just a restricted dimension range.

@informal thm:frontier-upper-all-d: The known-radius selector has worst-case mean-squared error at most \(C_\epsilon M^2 r_{n,d,\sigma}\) for all \(n,d\ge1\), \(M\ge1\), and \(0\le\sigma\le2\).

@formal thm:frontier-upper-all-d

---

## Lower bound

- The converse uses binary sparse-cell experiments as source problems.
- An affine map preserves cell masses and propensities while putting outcomes on scale \(M\).
- An exact-homogeneity source gives the collision baseline.
- A radius channel attenuates binary contrasts by \(\sigma/2\) and fits the radius constraint.
- Data processing transfers the binary testing difficulty through the channel.
- The two components combine inside the same real-outcome model class.

@figure lower-bound-transport: Box-and-arrow schematic showing exact binary sources and radius-channel binary sources transported into real-outcome lower bounds.

@informal prop:zeng-class-inclusion-and-lower-transfer: Binary source classes embed into the real-outcome classes, transferring exact-homogeneity and radius-channel lower bounds on the \(M\) scale.

@informal thm:radius-channel-converse-all-d: For every allowed \(n,d,M,\sigma\), the minimax risk is at least the all-alphabet lower benchmark with exact-homogeneity and radius-channel components.

@formal thm:radius-channel-converse-all-d

---

## Main result

- The lower side adds two irreducible costs: crossed-cell scarcity under homogeneity and radius-sensitive rare-cell difficulty.
- The upper side takes the best of polynomial estimation, collision estimation, and the zero branch.
- The bracket is stated over one same-index model class.

@formal thm:two-sided-minimax-bracket-all-d

---

## Endpoints

- At \(\sigma=0\), exact homogeneity gives the collision scale \(n^{-1}+\min(1,d/n^2)\).
- At \(\sigma=2\), the radius-indexed class equals the unrestricted-radius class.
- The unrestricted endpoint gives the large-alphabet polynomial scale \(n^{-1}+\min\{1,d^2/[n^2\log^2(en)]\}\).

@informal prop:endpoint-reductions-all-d: The bracket reduces to the exact-homogeneity rate at radius zero and the unrestricted large-alphabet rate at radius two.

@formal prop:endpoint-reductions-all-d

---

## Regimes

- For every fixed positive radius, the upper and lower benchmarks agree in order.
- They also agree in the saturated region.
- They agree when the polynomial term is dominated by the exact-homogeneity baseline.
- They agree when the squared radius is dominated by the exact-homogeneity baseline.
- The remaining region is a shrinking-radius wedge with intermediate alphabet size.

@figure phase-diagram: Box-and-arrow schematic showing the phase plane, polynomial branch, collision branch, zero branch, endpoint regimes, selector, and benchmark.

@informal thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d: Fixed positive radii, saturation, and parametric-dominance elbows have minimax risk within constants of the selector benchmark.

---

## Proof sketch

- Upper bound: split the sample, classify cells, and analyze heavy and light contributions conditionally on the pilot split.
- Light-cell control: Chebyshev coefficients approximate the rare-cell functional, and factorial statistics estimate the required moments.
- Collision control: crossed cells supply direct contrasts, while \(\sigma\) bounds the effect of cells that fail to cross.
- Lower bound: binary hard instances are embedded into real outcomes without changing the adjustment structure.
- Radius channel: attenuation by \(\sigma/2\) keeps alternatives inside the radius class and scales target separation.

---

## Also in the paper

@informal thm:robust-upper-construction-resolution: On the restricted dimension range, the polynomial and collision branches satisfy the same two constructive upper bounds.

@informal thm:frontier-upper: On the restricted dimension range, the known-radius selector has risk at most the stated frontier benchmark.

@informal thm:radius-channel-converse: On the restricted dimension range, the minimax risk is at least the parametric, exact-collision, and radius-channel lower benchmark.

@informal prop:endpoint-reductions: On the restricted dimension range, the endpoint expressions reduce to the exact-homogeneity and unrestricted-radius rates.

@informal thm:fixed-interior-tightness-and-shrinking-radius-gap: On the restricted dimension range, fixed interior radii and the parametric elbows match the selector benchmark.

@informal thm:two-sided-minimax-bracket: On the restricted dimension range, the same two-sided minimax bracket holds with the range condition.

@informal thm:published-binary-collision-comparison: Under the published binary collision guarantee, the selector remainder is at most the collision remainder, and it is asymptotically smaller when the polynomial remainder is negligible relative to the collision remainder.

---

## Conclusion

- We give a finite-sample minimax bracket for scalar ATE estimation with many discrete adjustment cells.
- The model allows arbitrary cell masses and real outcomes under fixed overlap, bounded conditional means, and bounded conditional second moments.
- The heterogeneity radius \(\sigma\) organizes the attainable risk.
- The known-radius selector is constructive and all-alphabet.
- The bracket is order matched at exact homogeneity, unrestricted radius, every fixed positive radius, saturation, and the parametric-dominance elbows.
