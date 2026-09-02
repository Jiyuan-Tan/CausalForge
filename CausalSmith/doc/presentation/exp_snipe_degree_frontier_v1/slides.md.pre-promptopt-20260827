# Minimax Error for Network Interference

Under Bernoulli assignment, bounded-degree low-order interference has minimax MSE of order \(B^2\min\{1,dA_d/n\}\) up to constants depending only on \((\beta,p)\), attained by clipped SNIPE and matched by complete-block lower bounds.

---

## Punchline

- The paper gives the finite-population minimax MSE frontier for estimating the all-treated-versus-all-control effect \(\tau_n\), the average total treatment contrast.
- The setting is known network interference, independent Bernoulli assignment, fixed interaction order \(\beta\), fixed treatment probability \(p\), and degree bound \(d\).
- The rate, up to constants depending only on \((\beta,p)\), is \(B^2\min\{1,dA_d/n\}\), where \(A_d\) is the complete-block Bernoulli score energy.
- Equivalently, for fixed \((\beta,p)\), the rate is \(B^2\min\{1,d\binom d{k_\star}/n\}\), where the exposed order \(k_\star\) is the largest interaction order whose Bernoulli contrast is nonzero.
- SNIPE weights each observed outcome by a centered Bernoulli score on that unit's neighborhood; clipping projects the result back to the target range, and the clipped estimator attains the rate up to the same constants.
- Complete directed blocks supply matching least-favourable designs.

---

## Why This Question Matters

- Network experiments often target a total treatment effect: what changes if everyone is treated instead of everyone controlled?
- With interference, each observed outcome can depend on neighbors' assignments, so unit-level Bernoulli randomization reveals the target only through local assignment variation.
- The practical question is how the mean squared error scales with network degree \(d\), population size \(n\), and interaction order \(\beta\).
- A running example is a product rollout on a social network, where a user's outcome depends on their own treatment and low-order combinations of treated neighbors.
- What is the best possible design-based error under this model?

---

## The Running Example

- Units are users in a known directed network.
- \(Z_j\) is user \(j\)'s treatment assignment, drawn independently with common treatment probability \(p\).
- \(N_i\) is the set of users whose assignments can enter user \(i\)'s outcome.
- The degree bound \(d\) says each outcome depends on at most \(d\) assignments, and each assignment can affect at most \(d\) outcomes.
- Low-order interference means outcomes use interactions among at most \(\beta\) assignments at a time.
- The target \(\tau_n\) compares the observed population under everyone treated versus everyone controlled.

---

## Setup: Design and Graph

- Potential outcomes are fixed finite-population objects.
- Randomness comes only from the Bernoulli assignment.
- The graph is known to the estimator.
- Self-loops count, so a user's own treatment can enter their outcome.
- The in-degree bound limits local exposure complexity.
- The out-degree bound limits how many estimator terms can share treatment coordinates.

@formal ass:bernoulli-design

@formal ass:bounded-degree

---

## Setup: Low-Order Outcomes

- Each \(Y_i(z)\) is a polynomial in the assignments inside \(N_i\).
- The interaction order \(\beta\) caps the degree of the monomials.
- The radius \(B\) is the unitwise coefficient-mass scale.
- In the rollout example, \(B\) bounds the total size of own-treatment, neighbor-treatment, and low-order interaction effects for each user.
- These assumptions define the coefficient-mass model class used in the first minimax frontier.

@formal ass:low-order

@formal ass:bounded-coefficient-mass

---

## The Estimator

- SNIPE weights each observed outcome by a centered Bernoulli score on that unit's neighborhood.
- Mechanism: for each unit, average \(Y_i^{\mathrm{obs}}\) against centered monomials up to the exposed order.
- The complete-block score energy \(A_d\) is the design second moment of the corresponding \(d\)-coordinate score.
- Clipping projects SNIPE back to the natural target range: \([-B,B]\) for the coefficient-mass class, and \([-2B,2B]\) for the uniformly bounded-outcome class introduced later.
- The statistical question becomes whether any estimator can improve the resulting MSE scale.

@figure estimator-pipeline: Schematic of the estimator: the known neighborhoods determine the centered Bernoulli scores, whose design second moment is \(A_d\); the scores are averaged against the observed outcomes, and projection clips that average to the bounded target range.

---

## Key Idea

- The difficulty separates into a local Bernoulli problem and a global network-overlap problem.
- Locally, \(A_d\) measures the cost of extracting the all-treated-versus-all-control contrast from Bernoulli variation inside one neighborhood.
- Globally, the extra factor \(d\) appears because one treatment coordinate can enter the scores of up to \(d\) units.
- The exposed order \(k_\star\) is the largest interaction order with nonzero Bernoulli contrast.
- For fixed \((\beta,p)\), \(A_d\) scales like \(\binom d{k_\star}\).

---

## Where the Literature Stands

- Design-based causal inference supplies the finite-population randomization framework.
- Interference work develops exposure mappings, graph-aware estimands, and IPW-style estimators for network experiments.
- Sparse and local interference work identifies neighborhood growth and overlap as central design quantities.
- Cortez-Rodriguez, Eichhorn, and Yu introduce low-order SNIPE under Bernoulli assignment and establish unbiasedness with variance bounds.
- This paper turns that low-order known-graph line into a bounded-class minimax frontier, with clipped SNIPE upper bounds and complete-block lower bounds.

---

## Main Result: Coefficient-Mass Frontier

@informal thm:degree-frontier: Under fixed \(\beta\ge1\) and \(0<p<1\), the coefficient-mass minimax MSE is bounded above and below, up to constants depending only on \((\beta,p)\), by \(B^2\min\{1,d\binom d{k_\star(d,\beta,p)}/n\}\), and clipped SNIPE attains the upper bound.

@formal thm:degree-frontier

---

## Why the Novelty Wins

- A direct unprojected score average has worst-case variance at most \(B^2dA_d/n\), the linear regime.
- That variance bound is informative only when \(dA_d/n\) is small.
- When \(dA_d/n\) exceeds one, the target itself is bounded by \(B\), so the risk saturates at scale \(B^2\); this is the saturated branch of the minimum.
- Clipping removes the excess risk contribution beyond the bounded target scale while preserving the linear-regime performance.
- The complete-block lower bound shows the same \(dA_d/n\) transition is intrinsic to the model class.

---

## Bounded-Outcome Frontier

- Two model classes are in play. The coefficient-mass class bounds each unit's total coefficient mass by \(B\); the uniformly bounded-outcome class instead bounds every potential outcome \(|Y_i(z)|\) by \(B\).
- The first class is contained in the second, and the inclusion is strict whenever \(B>0\) and \(d\ge1\).
- The interest is that the larger class does not pay a higher degree cost.

@informal thm:bounded-outcome-degree-frontier: Under fixed \(\beta\ge1\) and \(0<p<1\), the uniformly bounded-outcome minimax MSE has the same \(B^2\min\{1,dA_d/n\}\) scale up to constants depending only on \((\beta,p)\), and bounded-outcome clipped SNIPE attains the upper bound.

@formal thm:bounded-outcome-degree-frontier

---

## Complete-Block Benchmark

- Block-local design-unbiased linear estimators weight each unit's outcome by a function of its own block's assignments only, with weights required to be design-unbiased for the block contrast.
- On complete directed blocks this class has an exactly solvable minimax problem, so the leading constant is pinned rather than bounded.
- The optimum is characterized by the normalized block representer, the block score divided by its energy \(A_d\).

@informal thm:sharp-local-linear-constant-and-representers: On fixed complete directed block graphs with \(d_t\mid n_t\), the minimax risk over block-local design-unbiased linear estimators is exactly \(B^2A_{d_t}/m_t=B^2d_tA_{d_t}/n_t\).

@formal thm:sharp-local-linear-constant-and-representers

---

## Fair-Coin Calibration

@informal thm:fair-coin-energy-frontier: For \(p=1/2\), only odd-order Bernoulli contrasts contribute to \(A_d\), and first-order interference has minimax MSE at most and at least constant multiples of \(B^2\min\{1,d^2/n\}\).

@formal thm:fair-coin-energy-frontier

---

## Why the Upper Bound Works

- SNIPE is unbiased because centered Bernoulli monomials are orthogonal across different orders and recover the all-treated-versus-all-control contrast.
- The local variance contribution is controlled by \(A_d\), the complete-block score energy.
- Covariances appear when two unit scores share assignment coordinates.
- The out-degree bound turns each order-\(r\) overlap count into at most \(d\binom d r\).
- Summing over exposed orders gives the population scale \(B^2dA_d/n\).
- Projection converts this variance bound into a bound of order \(B^2\min\{1,dA_d/n\}\), with a constant depending only on \((\beta,p)\).

---

## Why the Lower Bound Works

- The construction partitions active units into complete directed \(d\)-blocks.
- Within each block, every active unit has the same full \(d\)-coordinate neighborhood.
- The perturbation direction is the normalized block representer \(h_d=g_d/A_d\), so its target contrast is large relative to its design energy.
- Two signed priors move the total effect in opposite directions by the same amount.
- Their Hellinger distance is calibrated by \(A_d/m\), so the two experiments remain statistically close at the claimed separation.
- This makes the minimax lower bound match the clipped-SNIPE upper bound.

@figure block-lower-bound: Complete directed blocks place all within-block arrows including loops, then two signed representer perturbations shift the total effect in opposite directions while keeping the induced experiments close.

---

## Takeaways

- The design-based minimax MSE frontier is of order \(B^2\min\{1,dA_d/n\}\), up to constants depending only on \((\beta,p)\), for bounded-degree low-order polynomial interference under common-probability Bernoulli assignment.
- The equivalent exposed-order scale is \(B^2\min\{1,d\binom d{k_\star(d,\beta,p)}/n\}\) for fixed \((\beta,p)\).
- Clipped SNIPE attains the frontier for the coefficient-mass and uniformly bounded-outcome classes.
- Complete directed blocks calibrate the matching lower bound and the exact local-linear benchmark.
- For fair-coin first-order interference \(A_d=4d\), and the frontier becomes \(B^2\min\{1,d^2/n\}\) up to absolute constants.
