# Minimax Error for Network Interference

We characterize the design-based minimax mean squared error for total treatment effects under known bounded-degree, low-order network interference and Bernoulli assignment.

---

## Overview

- We study the all-treated-versus-all-control effect \(\tau_n\), the finite-population average contrast between assigning everyone treatment and assigning everyone control.
- Outcomes may depend on neighbors' assignments through a low-order polynomial.
- The graph is known, and both in-degree and out-degree are bounded by \(d\).
- The treatment design is independent Bernoulli with common probability \(p\).
- The minimax mean squared error is governed by one local energy \(A_d\) and one graph-overlap charge \(d\).

@informal thm:degree-frontier: Under fixed \(\beta\ge1\) and \(0<p<1\), clipped SNIPE attains the coefficient-mass minimax risk up to constants depending only on \((\beta,p)\).

---

## Motivation

- Network experiments often target a total treatment effect, not only a direct effect.
- Under interference, one unit's outcome can depend on many assignments.
- Bernoulli assignment gives variation in many local exposure patterns, but those patterns are reused across overlapping neighborhoods.
- The practical question is: how much precision is possible when the graph is known and interference is low order?
- The answer matters for design planning: the degree \(d\) controls the finite-population price of interference.

---

## Running example

- Think of a platform experiment where each user is treated independently.
- A user's outcome can depend on their own assignment and on treated neighbors.
- Low-order interference means we allow individual and pairwise, or more generally fixed-order, neighborhood interactions.
- Bounded degree means each user has at most \(d\) relevant neighbors and can affect at most \(d\) outcomes.
- The estimand asks for the average change between turning treatment on for everyone and turning it off for everyone.

---

## Setup

- \(V_n\) is the finite population, and \(Z_j\) is unit \(j\)'s Bernoulli treatment assignment.
- \(N_i\) is the directed interference neighborhood of unit \(i\).
- \(Y_i(z)\) is a polynomial in assignments inside \(N_i\), with interaction order at most \(\beta\).
- \(B\) is the radius of the bounded coefficient-mass or bounded-outcome class.
- \(\tau_n\) is the all-treated-versus-all-control total treatment effect.
- Risk averages over the random assignment, with the graph and potential outcomes fixed.

---

## Assumptions

- Common-probability Bernoulli assignment: units are independently treated with probability \(p\in(0,1)\).
- Bounded interference degree: every neighborhood has size at most \(d\), and every assignment coordinate enters at most \(d\) neighborhoods.
- Low-order outcomes: only monomials of degree at most \(\beta\) enter each potential outcome.
- Coefficient-mass envelope: each unit's polynomial coefficients have total absolute mass at most \(B\).
- In the running example, \(d\) is the maximum measured local spillover degree, and \(\beta\) is the modeled interaction complexity.

---

## SNIPE mechanism

- SNIPE is the low-order polynomial interference estimator of Cortez-Rodriguez et al. (2023).
- Mechanism: for each unit, weight the observed outcome by centered Bernoulli monomials over its neighborhood.
- The score is calibrated so its design expectation recovers the all-treated-versus-all-control contrast for every low-order monomial.
- The clipped version projects the estimate into the natural bounded range.
- Clipping is what lets the same estimator cover the saturated minimax branch.

@figure estimator-pipeline: Box-and-arrow schematic from known neighborhoods and observed outcomes through centered Bernoulli monomial scores and the score energy \(A_d\) to the weighted SNIPE average, clipping, and the worst-case MSE question.

---

## Key idea

- The local difficulty is summarized by the complete-block score energy \(A_d\).
- \(A_d\) measures how much Bernoulli variation is needed to extract the all-treated-versus-all-control contrast inside one \(d\)-unit neighborhood.
- The global difficulty adds one graph charge: an assignment coordinate can appear in up to \(d\) unit-level scores.
- The exposed order \(k_\star(d,\beta,p)\) is the largest interaction order with nonzero Bernoulli contrast.
- For fixed \((\beta,p)\), the frontier is the local exposed-interaction count times the overlap charge.

@informal lem:block-energy-representer: The complete-block energy is comparable to the exposed binomial term, and the normalized block representer solves the local contrast problem.

---

## Related literature

- Horvitz and Thompson (1952), Rubin (1978), and Imbens and Rubin (2015) provide the finite-population design-based language.
- Manski (1993), Sobel (2006), Hudgens and Halloran (2008), and Aronow and Samii (2017) develop core interference frameworks.
- Leung (2022), Sävje et al. (2021), Hu et al. (2022), and Gao and Ding (2025) emphasize local interference, exposure, and graph-aware design.
- Cortez-Rodriguez et al. (2023) introduce and analyze SNIPE for low-order neighborhood interference under Bernoulli assignment.
- Our contribution gives the bounded-class minimax calibration for this known-graph, low-order Bernoulli setting.

---

## Main result I

@informal thm:degree-frontier: Over the coefficient-mass class, the minimax mean squared error is between constant multiples of the exposed-binomial scale, and clipped SNIPE attains the upper bound.

@formal thm:degree-frontier

---

## Reading the rate

- The coefficient-mass frontier has scale \(B^2\) times a design difficulty term.
- The term \(A_d\) is local: it comes from one complete \(d\)-block.
- The extra \(d\) is global: it counts possible overlap among neighborhoods.
- The exposed-binomial form replaces \(A_d\) by the number of visible interaction subsets at order \(k_\star(d,\beta,p)\).
- In the running example, more local spillover links raise error through both more local interactions and more shared assignment coordinates.

---

## Main result II

@informal thm:bounded-outcome-degree-frontier: The uniformly bounded-outcome class has the same minimax degree dependence as the coefficient-mass class, and its clipped SNIPE estimator attains the rate up to constants depending only on \((\beta,p)\).

@formal thm:bounded-outcome-degree-frontier

---

## Complete blocks

- Complete directed \(d\)-blocks are the hardest local graph shape used in the lower bound.
- Inside a block, every active unit has the full \(d\)-coordinate neighborhood.
- The least-favourable construction perturbs coefficients along the normalized block representer.
- The two signed perturbations separate the total effect while keeping the induced laws close.
- When \(d\mid n\), the same blocks give an exact worst-case risk for unprojected SNIPE.

@figure block-construction: Box-and-arrow schematic from complete directed blocks to representer perturbations, then signed priors, then separated total effects with close assignment laws.

---

## Local linear benchmark

@informal thm:sharp-local-linear-constant-and-representers: On fixed complete directed block graphs, the minimax risk over block-local design-unbiased linear estimators is exactly \(B^2A_{d_t}/m_t\).

@formal thm:sharp-local-linear-constant-and-representers

---

## Fair coin

@informal thm:fair-coin-energy-frontier: For \(p=1/2\), even-order Bernoulli contrasts vanish, and first-order interference has minimax risk at most and at least constant multiples of \(B^2\min\{1,d^2/n\}\).

@formal thm:fair-coin-energy-frontier

---

## Proof sketch

- Upper bound: SNIPE is design-unbiased because centered Bernoulli monomials are orthogonal across orders.
- Variance bound: covariance terms appear only when neighborhoods share assignment coordinates.
- Overlap count: bounded out-degree turns each order-\(r\) overlap into at most \(d\binom d r\) shared terms.
- Lower bound: complete blocks align neighborhoods so the block representer creates the hardest local contrast.
- Testing step: two signed block priors keep the observed-data laws close while moving \(\tau_n\) apart.
- The same \(A_d\) appears in the estimator variance and in the lower-bound affinity.

---

## Takeaways

- We characterize the finite-population minimax mean squared error for known bounded-degree, low-order polynomial network interference under Bernoulli assignment.
- The frontier is controlled by local block energy \(A_d\), exposed order \(k_\star(d,\beta,p)\), and one out-degree overlap charge \(d\).
- Clipped SNIPE attains the bounded-class minimax rate over both coefficient-mass and uniformly bounded-outcome envelopes.
- Complete directed blocks calibrate the lower bound, the exact unprojected SNIPE risk, and the local linear benchmark.
- For fair coins and first-order interference, the frontier specializes to \(B^2\min\{1,d^2/n\}\) up to constants.
