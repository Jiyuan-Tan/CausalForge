# Graph-Adaptive Bernoulli Design

We choose heterogeneous Bernoulli treatment probabilities from the bipartite graph, then use the same graph-only criterion for design and conservative inference on the all-treated-versus-all-control effect.

---

## Overview

- In bipartite experiments, interventions are assigned on \(I_n\), while outcomes are measured on \(O_n\).
- Each outcome sees only its intervention neighborhood \(N_i(G_n)\).
- We choose independent Bernoulli probabilities \(p_k\), one per intervention unit.
- The target is \(\tau_n\), the finite-population mean contrast between all-treated and all-control neighborhood outcomes.
- The design criterion is a computable graph envelope for the Hájek linearization variance.
- The payoffs are an optimal feasible design, asymptotic normality, and conservative Wald intervals.

---

## Motivation

- Think of ads assigned to advertisers and outcomes measured on users.
- A user may be adjacent to several advertisers, so treatment exposure is a neighborhood event.
- Homogeneous Bernoulli assignment treats every advertiser with the same probability.
- The graph can make some intervention units much more important for exposure overlap than others.
- A fixed expected-treatment budget asks: where should probability mass go?
- The design should be chosen before outcomes are observed.

@figure bipartite-overlap: Box-and-arrow schematic where intervention units \(I_n\) and outcome units \(O_n\) feed the known bipartite graph \(G_n\), whose intervention neighborhoods \(N_i(G_n)\) and shared neighborhoods induce the outcome-overlap graph.

---

## Related literature

- We work in the design-based tradition of Neyman (1923), Horvitz and Thompson (1952), and Hájek (1964).
- Interference estimands and exposure mappings build on Hudgens and Halloran (2008), Liu and Hudgens (2014), and Aronow and Samii (2017).
- Network and bipartite designs include Zigler and Papadogeorgou (2018), Chattopadhyay et al. (2023), and Lu et al. (2025).
- Clustered approaches such as Ugander and Yin (2020) and Brennan et al. (2022) change assignment dependence.
- Our design keeps independent assignment and adapts the marginal probabilities to the graph.

---

## Setup

- \(I_n\) is the set of intervention units, with size \(m_n\).
- \(O_n\) is the set of outcome units, with size \(n\).
- \(G_n\) is the known bipartite graph.
- \(N_i(G_n)\) is outcome \(i\)'s intervention neighborhood.
- \(d_i=|N_i(G_n)|\) measures outcome-side exposure complexity.
- \(s_k\) measures intervention-side incidence, the number of outcomes adjacent to intervention \(k\).

@formal ass:bipartite-interference

---

## Assignment design

- We use independent Bernoulli assignment with heterogeneous probabilities \(p_k\).
- The positivity floor \(\epsilon\) keeps exposure probabilities stable.
- The budget \(B_n\) fixes the expected number of treated intervention units.
- Feasible designs reallocate treatment probability inside a probability box while preserving total intensity.

@formal ass:independent-heterogeneous-bernoulli

@formal ass:positivity-floor

@formal ass:budget-balance

---

## Estimation target

- \(Y_i^1\) is outcome \(i\)'s all-treated neighborhood potential outcome.
- \(Y_i^0\) is outcome \(i\)'s all-control neighborhood potential outcome.
- \(\mu_1\) and \(\mu_0\) average these quantities over \(O_n\).
- \(\tau_n=\mu_1-\mu_0\) is the finite-population estimand.
- The Hájek estimator normalizes inverse-probability weighted all-treated and all-control exposure means.

@formal def:hetero-hajek-estimator

---

## Graph envelope

- The linearization summand \(\eta_i(p,Z)\) captures the first-order contribution of outcome \(i\).
- Pairs of outcomes matter when their intervention neighborhoods overlap.
- The graph envelope replaces unknown outcome contrasts with the bounded-outcome worst case.
- It is known at design time from \(G_n\) and \(p\).

@formal def:graph-envelope

@informal thm:hetero-envelope: Under independent heterogeneous Bernoulli assignment and bounded potential outcomes, the linearization variance scale is at most the graph envelope.

---

## Homogeneous benchmark

- Homogeneous Bernoulli assignment is the special case \(p_k=p\) for all intervention units.
- Then the same-exposure covariance loads depend on shared-neighborhood size.
- This benchmark connects the heterogeneous analysis to the existing homogeneous bipartite framework.

@informal prop:homogeneous-reduction: With a constant Bernoulli probability, the variance representation reduces to overlap-count covariance loads and the corresponding homogeneous variance formula.

---

## Optimal design

- We choose \(p\) by minimizing \(V_{\mathrm{env}}(G_n,p)\) over the positivity-constrained budget set.
- The objective is convex on the feasible design class.
- The optimizer \(p_n^*(G_n)\) is computable through standard convex optimization.
- The KKT conditions say that interior intervention units equalize the envelope gradient score up to the budget multiplier.

@formal thm:convex-design

---

## Key idea

- The naive homogeneous rule assigns probability by capacity alone.
- The envelope score asks how changing \(p_k\) affects all overlapping outcome pairs involving intervention \(k\).
- Moving probability from a high-score coordinate to a low-score coordinate lowers the envelope when the score spread is positive.
- The quantitative gain is controlled by the score spread \(\Delta_g\), the feasible movement allowed by \(\epsilon\), and the directional modulus \(L_{ab}\).
- In singleton-neighborhood graphs, the score is proportional to \(s_k^2\left((1-\rho)^{-2}-\rho^{-2}\right)\).

---

## Main result

@informal thm:heterogeneity-separation: Under an admissible budget with \(\epsilon<\rho<1-\epsilon\) and \(\rho\neq 1/2\), unequal homogeneous-point gradient scores imply a strictly smaller envelope at every envelope-optimal heterogeneous design.

@formal thm:heterogeneity-separation

---

## Inference guarantees

- For inference, the relevant asymptotic regime has bounded outcomes, bounded outcome degree, bounded overlap dependency, uniform positivity, and nondegenerate variance.
- Bounded outcome degree controls exposure weights.
- Bounded overlap dependency gives a sparse dependency graph for the linearized summands.
- The Hájek estimator is asymptotically equivalent to its linearization and then normal after scaling.
- The same envelope used for design also supplies the conservative variance scale.
- The guarantee is design based: potential outcomes are fixed, and probability is over assignment.

@formal thm:hetero-clt

@formal thm:postdesign-wald

---

## Surrogate design

- The exact envelope couples probabilities across shared neighborhoods.
- The surrogate replaces that coupled objective with additive weights \(h_k(G_n)\).
- Mechanism: each intervention unit receives a graph-derived weight and minimizes \(h_k(G_n)\{p_k^{-1}+(1-p_k)^{-1}\}\) inside the shared budget.
- Under bounded outcome degree, this separable design has a uniform envelope approximation certificate.

@informal thm:surrogate-certificate: With admissible \(\epsilon\), bounded outcome degree \(\bar d\), and an admissible budget, the surrogate approximation ratio is at most \(\max\!\left\{1,\epsilon^{-(\bar d-1)}\right\}\).

@formal thm:surrogate-certificate

---

## Surrogate scope

- The bounded-degree condition is the structural reason the surrogate tracks the full envelope.
- Intervention-side degree summaries alone miss higher-order shared-neighborhood patterns.
- The unbounded-degree construction gives sequences where the surrogate approximation ratio diverges despite degree-dispersion and \(h\)-weight-ratio controls.

@informal thm:dispersion-certificate-unbounded: For every admissible \(\epsilon\), dispersion constant, and \(h\)-weight ratio constant, there are unbounded-degree sequences with approximation ratio tending to infinity.

@formal thm:dispersion-certificate-unbounded

---

## Proof sketch

- First, condition on the graph and treat potential outcomes as fixed.
- Exposure indicators for two outcomes are independent when their neighborhoods are disjoint.
- Shared neighborhoods produce the pairwise covariance loads in the envelope.
- Bounded outcomes turn those loads into a uniform variance upper bound.
- Convexity follows from reciprocal-product terms over the positivity box.
- The central limit theorem follows from bounded summands and bounded dependency degree.

@informal lem:bounded-degree-dependency-clt: Centered, uniformly bounded summands with bounded dependency degree and linear variance growth are asymptotically normal after variance scaling.

---

## Design workflow

@figure design-pipeline: Box bipartite graph \(G_n\) points to box compute envelope \(V_{\mathrm{env}}\); box compute envelope \(V_{\mathrm{env}}\) points to box choose \(p_n^*(G_n)\); box choose \(p_n^*(G_n)\) points to box run Bernoulli experiment; box run Bernoulli experiment points to box Hájek estimate and Wald interval.

- Fix \(B_n\) from treatment capacity and choose an admissible positivity floor.
- Audit \(d_i\), \(s_k\), and outcome-overlap degrees.
- Compare homogeneous assignment, the exact envelope minimizer, and the surrogate.
- Report the envelope value, exposure support diagnostics, KKT residuals, and surrogate ratio.
- Interpret at least one result through the graph diagnostics before randomization.

---

## Takeaways

- We construct graph-adaptive independent Bernoulli designs for bipartite interference experiments.
- The variance envelope is observable before assignment and valid uniformly over bounded potential-outcome schedules.
- The feasible design problem is convex and has an optimality characterization.
- The envelope-optimal design supports asymptotic Hájek normality and conservative Wald coverage under bounded local dependence.
- The surrogate gives a separable approximation with a bounded-degree certificate.
