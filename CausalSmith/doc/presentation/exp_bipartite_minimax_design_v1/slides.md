# Graph-Adaptive Bernoulli Design for Bipartite Interference

TL;DR: Choose independent treatment probabilities from the observed bipartite graph to minimize a computable variance envelope, then use that same graph-only scale for conservative design-based inference.

---

## The Punchline

- The paper studies experiments with intervention units on one side and outcome units on the other.
- The estimand \(\tau_n\), the finite-population all-treated-versus-all-control effect, is estimated with an exposure-weighted Hájek estimator.
- The design choice is the heterogeneous Bernoulli vector \(p\), subject to a positivity floor and a fixed expected-treatment budget.
- The paper constructs \(V_{\mathrm{env}}(G_n,p)\), a graph-and-design envelope for the Hájek linearization variance.
- Minimizing this envelope gives a convex, feasible, graph-adaptive design.
- Under bounded local dependence, the resulting Wald interval has asymptotically conservative coverage.

---

## Why This Design Problem Matters

- In a bipartite experiment, treatment happens at one set of units, while outcomes are measured elsewhere.
- A running example is a platform experiment: suppliers receive an intervention, and customer outcomes depend on the suppliers connected to each customer.
- Full exposure is rare when an outcome has several treated-side neighbors.
- Equal treatment probabilities can spend budget where they create little exposure information.
- The question is: how should a fixed treatment budget be allocated across intervention units before outcomes are observed?

---

## The Graph Creates the Exposure Problem

- Everything the design can react to is read off the observed graph, so it is worth naming the few graph quantities that will do the work.
- \(I_n\) is the intervention-unit set, \(O_n\) is the outcome-unit set, and \(G_n\) is the known bipartite graph.
- \(N_i(G_n)\) is outcome \(i\)'s intervention neighborhood.
- \(d_i\) counts how many intervention assignments enter outcome \(i\)'s exposure.
- \(s_k\) counts how many outcome units are incident to intervention unit \(k\).
- \(S_{ij}(G_n)\) is the shared intervention neighborhood of outcomes \(i\) and \(j\).
- \(\Delta_n\) bounds how many outcome exposure terms can depend on a given one.

@figure bipartite-overlap-graph: The diagram traces how the observed bipartite graph generates the design-relevant quantities — outcome neighborhoods and their degrees, intervention-side incidence counts, shared neighborhoods, the induced outcome-overlap graph, and the dependency bound it carries.

---

## Assignment and Exposure

- Each intervention unit \(k\) receives treatment independently with probability \(p_k\).
- \(T_i(Z)\) indicates that every intervention in \(N_i(G_n)\) is treated.
- \(C_i(Z)\) indicates that every intervention in \(N_i(G_n)\) is untreated.
- The estimator compares normalized inverse-probability-weighted all-treated and all-control exposure means.
- In the platform example, a customer is all-treated only when every connected supplier is treated.

@formal ass:bipartite-interference

@formal ass:independent-heterogeneous-bernoulli

---

## Feasible Designs

- The experimenter fixes a positivity floor \(\epsilon\), so every intervention unit retains assignment support.
- The experimenter also fixes \(B_n\), the expected number of treated intervention units.
- The feasible class is the probability box intersected with the budget hyperplane.
- Heterogeneity means reallocating probability mass across intervention units while preserving total expected treatment.

@formal ass:positivity-floor

@formal ass:budget-balance

---

## Large-Sample Regularity

- Potential outcomes are fixed; randomization is the only source of randomness.
- Bounded outcomes keep exposure-weighted summands controlled.
- Bounded outcome degree keeps exposure probabilities from collapsing under positivity.
- Bounded overlap dependency gives the linearized summands a sparse dependency graph.
- Nondegenerate variance supplies the scale needed for a normal approximation.

@formal ass:bounded-outcomes

@formal ass:bounded-outcome-degree

@formal ass:bounded-overlap-dependency

@formal ass:variance-nondegenerate

---

## Key Idea: Optimize the Worst-Case Variance Scale

- The exact variance depends on unknown potential-outcome contrasts.
- The graph tells us which exposure indicators move together.
- The envelope replaces unknown outcome contrasts by the bounded-outcome worst case.
- The design criterion is therefore observable before randomization.
- The novelty is to optimize heterogeneous independent Bernoulli probabilities against this graph-only envelope.

---

## Where the Literature Stands

- Neyman, Horvitz-Thompson, and Hájek give the finite-population design-based foundation.
- General interference work defines exposure mappings and randomization-based estimation.
- Network and bipartite designs often use clustering or outcome-model structure to improve exposure and power.
- Homogeneous Bernoulli bipartite inference supplies a direct benchmark.
- This paper keeps independent assignment and lets the observed graph determine heterogeneous assignment probabilities.

---

## Benchmark: Homogeneous Bernoulli Assignment

@informal prop:homogeneous-reduction: With a common assignment probability, same-exposure covariance loads depend on shared-neighborhood size, and the variance scale reduces to the homogeneous Bernoulli expression.

@formal prop:homogeneous-reduction

---

## Main Result 1: The Heterogeneous Envelope

@informal thm:hetero-envelope: Under positive assignment probabilities, independent heterogeneous Bernoulli assignment, and bounded outcomes, the linearization covariance has a pairwise graph-and-design representation and the variance scale is at most \(V_{\mathrm{env}}(G_n,p)\).

@formal thm:hetero-envelope

---

## Main Result 2: The Design Problem Is Convex

@informal thm:convex-design: Under an admissible positivity margin and budget, the feasible design set is nonempty, compact, and convex, the graph envelope is convex, and an envelope-optimal design exists with KKT conditions.

@formal thm:convex-design

---

## Why the Novelty Wins

- A homogeneous design gives every intervention unit the same probability \(\rho=B_n/m_n\).
- The envelope gradient score \(g_k(G_n,p)\) measures the marginal variance-envelope cost of probability at intervention unit \(k\).
- When scores differ at \(p^{\mathrm{hom}}\), shifting budget from a high-score coordinate to a low-score coordinate lowers the envelope.
- The improvement is controlled by \(\Delta_g\), the score spread, and \(L_{ab}\), the directional curvature along the budget-preserving move.
- In singleton-neighborhood graphs, the diagnostic becomes transparent: score differences track heterogeneity in \(s_k^2\) when \(\rho\neq 1/2\).

@informal thm:heterogeneity-separation: Under the stated admissible-budget and homogeneous-rate conditions, unequal homogeneous-point gradient scores imply strict envelope improvement by a heterogeneous design, with a quantitative lower bound.

@formal thm:heterogeneity-separation

---

## Main Result 3: Design-Based Inference

@informal thm:hetero-clt: Under the stated interference, boundedness, bounded-degree, bounded-dependency, feasibility, optimality, positivity, and nondegenerate-variance conditions, the envelope-optimal Hájek estimator is asymptotically normal after linearization.

@formal thm:hetero-clt

@informal thm:postdesign-wald: Under the stated design and graph regularity conditions, \(V_{\mathrm{env}}(G_n,p_n)\) upper-bounds the variance scale and yields asymptotically conservative Wald coverage.

@formal thm:postdesign-wald

---

## A Tractable Surrogate

- The exact envelope couples probabilities across shared neighborhoods.
- The surrogate assigns each intervention unit a graph weight \(h_k(G_n)\) and minimizes an additive reciprocal-probability objective.
- This removes cross-coordinate coupling while preserving a graph-based allocation signal.
- Under bounded outcome degree, the surrogate objective and the exact envelope are comparable up to an explicit factor.
- The approximation ratio \(\alpha_{\mathrm{cert}}(G_n)\) is the surrogate design's envelope value divided by the envelope-optimal design's, so a bound on it prices the loss from using the surrogate.

@informal thm:surrogate-certificate: Under an admissible floor, bounded outcome degree, and an admissible budget, the surrogate objective is within the displayed multiplicative envelope bounds, and \(\alpha_{\mathrm{cert}}(G_n)\) is at most \(\max\{1,\epsilon^{-(\bar d-1)}\}\).

@formal thm:surrogate-certificate

---

## Also in the Paper

@informal thm:dispersion-certificate-unbounded: For any fixed positivity floor, dispersion threshold, and \(h\)-weight ratio bound, there are graph sequences meeting those controls along which the surrogate approximation ratio still diverges.

@informal lem:bounded-degree-dependency-clt: For bounded centered summands with fixed dependency degree and linearly growing variance, the normalized sum converges to a standard normal distribution.

---

## Why the Results Are True

- The covariance calculation starts from exposure indicators, whose dependence is completely determined by shared intervention neighbors.
- Bounded potential outcomes convert the covariance representation into a uniform graph-only upper envelope.
- Convexity comes from reciprocal probability products on the positivity box plus the affine budget constraint.
- The CLT follows because bounded outcome degree and bounded overlap dependency turn the Hájek linearization into a bounded sparse-dependence sum.
- The Wald result uses the same normal approximation with the deterministic envelope as a conservative scale.

---

## Takeaways

- The paper establishes a graph-adaptive independent Bernoulli design for bipartite interference experiments.
- The design targets \(\tau_n\), the finite-population all-treated-versus-all-control effect, through an exposure-weighted Hájek estimator.
- The graph envelope gives an observable design-stage objective and a conservative post-design variance scale.
- The optimal design exists through a convex program and can strictly improve on homogeneous assignment when graph overlap scores differ.
- The separable surrogate has an explicit bounded-degree approximation certificate.
