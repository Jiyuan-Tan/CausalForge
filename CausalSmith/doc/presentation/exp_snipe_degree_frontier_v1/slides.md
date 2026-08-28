# Minimax Risk Under Network Interference

Under fixed interaction order and common Bernoulli assignment, the minimax MSE for the all-treated-versus-all-control effect is governed by one local score energy and one graph-overlap charge.

---

## The paper identifies the design cost of network interference

- The target is \(\tau_n\), the finite-population all-treated-versus-all-control average effect.
- Outcomes may depend on neighbors' assignments through a known directed graph.
- Each neighborhood has degree at most \(d\), and each assignment can affect at most \(d\) outcomes.
- Potential outcomes are low-order polynomials with interaction order \(\beta\).
- The minimax MSE scale is \(B^2\min\{1,dA_d/n\}\).
- Equivalently, for fixed \((\beta,p)\), the scale is \(B^2\min\{1,d\binom d{k_\star(d,\beta,p)}/n\}\).

---

## A simple experiment already shows the difficulty

- Imagine a product experiment where each user is treated independently with probability \(p\).
- A user's outcome can depend on the user's own treatment and up to \(d-1\) neighbors' treatments.
- The estimand compares the world where everyone is treated with the world where everyone is controlled.
- The realized experiment observes only one mixed-treatment assignment.
- The question is: how much Bernoulli variation is enough to estimate the full-population contrast?

@figure experiment-to-target: A box-and-arrow schematic with boxes labeled Bernoulli assignment, network neighborhoods, observed outcomes, and all-treated-versus-all-control target.

---

## The graph contributes an overlap charge

- The in-degree bound says each outcome uses at most \(d\) assignment coordinates.
- The out-degree bound says each assignment coordinate can enter at most \(d\) outcomes.
- Variance grows when two unit-level scores share assignment coordinates.
- The paper's overlap count turns this graph fact into one extra factor of \(d\).
- The remaining difficulty is local: estimating one neighborhood's all-treated-versus-all-control contrast.

---

## The design and graph assumptions fix the probability law

@formal ass:bernoulli-design

@formal ass:bounded-degree

---

## The outcome model fixes the local complexity

@formal ass:low-order

@formal ass:bounded-coefficient-mass

- \(B\) is the unitwise coefficient-mass radius.
- In the running experiment, \(\beta=1\) allows own and neighbor main effects; larger fixed \(\beta\) allows low-order interactions among treated neighbors.
- The all-treated-versus-all-control effect \(\tau_n\) averages the contrast \(Y_i(\mathbf 1)-Y_i(\mathbf 0)\) across units.

---

## The exposed order is what Bernoulli assignment can see

- \(\Delta_r(p)\), the order-\(r\) Bernoulli contrast coefficient, tells whether an \(r\)-way centered monomial contributes to the target contrast.
- \(\bar\beta_d=\min\{\beta,d\}\) is the largest interaction order available inside a degree-\(d\) neighborhood.
- \(k_\star(d,\beta,p)\) is the largest available order with nonzero Bernoulli contrast.
- The local score energy \(A_d\) is comparable to \(\binom d{k_\star(d,\beta,p)}\) for fixed \((\beta,p)\).

@formal def:exposed-order

---

## SNIPE estimates the target by matching centered contrasts

- Mechanism: SNIPE weights each observed outcome by centered neighborhood monomials up to order \(\bar\beta_d\), scaled by the corresponding Bernoulli contrasts.
- The unprojected estimator is design-unbiased on the low-order model classes.
- The clipped estimator projects the SNIPE average back to the natural bounded range.
- The central question becomes whether clipped SNIPE has the best possible worst-case MSE.

@figure snipe-pipeline: A box-and-arrow schematic with boxes labeled observed assignment and outcomes, centered neighborhood score, SNIPE average, clipped estimate, and total-effect target.

---

## The main frontier matches upper and lower bounds

@informal thm:degree-frontier: Under fixed \(\beta\ge1\), \(0<p<1\), \(d\le n\), and \(B\ge0\), the coefficient-mass minimax risk is between constants times \(B^2\min\{1,d\binom d{k_\star(d,\beta,p)}/n\}\), and clipped SNIPE attains the upper bound.

@formal thm:degree-frontier

---

## The rate has a local factor and a network factor

- \(A_d\) is the local Bernoulli score energy for one complete \(d\)-neighborhood.
- \(d\) is the global overlap charge from shared assignment coordinates across unit scores.
- \(n^{-1}\) is the population averaging gain.
- Projection gives the saturated branch \(B^2\) when the linear variance scale is large.
- In the running first-order fair-coin example, the frontier becomes \(B^2\min\{1,d^2/n\}\).

---

## Complete blocks calibrate the lower bound

- The least-favourable construction partitions active units into complete directed \(d\)-blocks.
- Inside each block, every active unit has the same full \(d\)-coordinate neighborhood.
- The perturbation direction is the normalized block representer \(h_d\).
- The two signed block priors separate the total effect by \(\rho\delta\) while keeping Hellinger distance controlled by \(A_d/m\).
- This produces the same \(dA_d/n\) scale as the SNIPE upper bound.

---

## Bounded outcomes have the same degree dependence

@informal thm:bounded-outcome-degree-frontier: Under fixed \(\beta\ge1\), \(0<p<1\), \(d\le n\), and \(B\ge0\), the coefficient-mass and uniformly bounded-outcome minimax risks share the scale \(B^2\min\{1,dA_d/n\}\), and the bounded-outcome clipped SNIPE estimator attains the upper bound.

@formal thm:bounded-outcome-degree-frontier

---

## Complete blocks give an exact SNIPE variance benchmark

- When \(d\mid n\), there are \(m=n/d\) complete directed blocks.
- On these blocks, canonical unprojected SNIPE has exact worst-case MSE \(B^2A_d/m\).
- The same value equals \(B^2dA_d/n\).
- This exact calculation explains why the global upper and lower bounds use the same block energy.

---

## Local linear weights have an exact block value

@informal thm:sharp-local-linear-constant-and-representers: On fixed complete directed \(d_t\)-block graphs with product Bernoulli assignment and coefficient-mass radius \(B>0\), the minimax risk over block-local design-unbiased linear estimators equals \(B^2A_{d_t}/m_t=B^2d_tA_{d_t}/n_t\).

@formal thm:sharp-local-linear-constant-and-representers

---

## Fair coins expose odd orders

@informal thm:fair-coin-energy-frontier: For \(p=1/2\), even-order Bernoulli contrasts vanish, \(A_d=4\sum_{1\le r\le\bar\beta_d,\ r\text{ odd}}\binom dr\), and the first-order frontier is between constants times \(B^2\min\{1,d^2/n\}\).

@formal thm:fair-coin-energy-frontier

---

## The proof rests on three finite-population facts

- Orthogonality: centered Bernoulli monomials make the SNIPE score recover the all-treated-versus-all-control contrast.
- Overlap counting: bounded out-degree limits how many score covariances can share a treatment subset.
- Block calibration: complete directed blocks align neighborhoods so the representer energy \(A_d\) controls both separation and distinguishability.
- Together, these facts match the clipped-SNIPE upper bound with the least-favourable lower bound.

---

## The contribution is a minimax calibration for low-order interference

- The paper characterizes the bounded-class design minimax MSE for total-effect estimation under known bounded-degree low-order polynomial interference.
- The frontier is \(B^2\min\{1,dA_d/n\}\), equivalently \(B^2\min\{1,d\binom d{k_\star(d,\beta,p)}/n\}\) up to constants depending on \((\beta,p)\).
- Clipped SNIPE attains the frontier over both coefficient-mass and uniformly bounded-outcome classes.
- Complete directed blocks provide the matching lower-bound calibration and exact unprojected-SNIPE benchmark.
- The local linear complete-block problem has exact value \(B^2A_{d_t}/m_t\).
