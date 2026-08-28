# Graph-Adaptive Bernoulli Design for Bipartite Interference

Under bounded local overlap, the paper constructs graph-adaptive Bernoulli probabilities that minimize a computable variance envelope and support conservative Wald inference for \(\tau_n\), the all-treated-versus-all-control finite-population effect.

---

## The graph can guide treatment probabilities before outcomes are observed

- The experiment has intervention units that receive treatment and outcome units that respond through known neighborhoods.
- Independent Bernoulli assignment is operationally simple, but equal probabilities can waste exposure support on the wrong parts of the graph.
- The paper chooses heterogeneous probabilities \(p_k\), one for each intervention unit, before seeing outcomes.
- The design target is a graph-only upper envelope for the Hájek linearization variance.
- The payoff is a feasible design rule, a variance scale for inference, and conditions for conservative coverage.

@informal thm:convex-design: Under an admissible positivity floor and expected-treatment budget, the graph-envelope minimization problem has a feasible convex solution.

---

## A bipartite experiment creates local exposure dependence

- Think of ads shown to users and purchases measured in markets, or policies applied to providers and outcomes measured for patients.
- \(I_n\) is the intervention-unit set; \(O_n\) is the outcome-unit set.
- The known bipartite graph \(G_n\) tells which interventions can affect each outcome.
- \(N_i(G_n)\), the neighborhood of outcome \(i\), is the set of intervention units whose assignments enter that outcome.
- Two outcomes become statistically linked when their neighborhoods share at least one intervention.

@figure bipartite-overlap: Box-and-arrow schematic showing intervention units \(I_n\) pointing to outcome neighborhoods \(O_n\), and shared intervention neighborhoods pointing to an induced outcome-overlap graph.

---

## The estimand compares two neighborhood exposure worlds

- Each outcome has a fixed potential-outcome schedule indexed by its neighborhood assignment.
- \(Y_i^1\) is outcome \(i\)'s value when every intervention in \(N_i(G_n)\) is treated.
- \(Y_i^0\) is outcome \(i\)'s value when every intervention in \(N_i(G_n)\) is control.
- \(\tau_n\), the finite-population estimand, is the mean of \(Y_i^1\) minus the mean of \(Y_i^0\).
- Randomness comes only from assignment.

@formal ass:bipartite-interference

---

## Assignment is independent but graph adaptive

- Each intervention unit \(k\) receives treatment independently with probability \(p_k\).
- The probability vector \(p\) can vary across the graph.
- A positivity floor \(\epsilon\), the common lower and upper probability margin, keeps exposure weights stable.
- A budget \(B_n\), the expected number treated, fixes total treatment capacity.
- The design task reallocates probability mass across \(I_n\) while preserving that capacity.

@formal ass:independent-heterogeneous-bernoulli

---

## The feasible class encodes overlap and capacity

- Feasible probabilities stay between \(\epsilon\) and \(1-\epsilon\).
- Their sum equals the treatment budget \(B_n\).
- The homogeneous benchmark sets every probability to \(\rho=B_n/m_n\), the budget share.
- The graph-adaptive design searches over the same feasible class.
- In the running example, the same ad capacity or provider-treatment capacity is reallocated across graph positions.

@formal def:feasible-designs

---

## The Hájek estimator uses realized all-treated and all-control exposures

- \(T_i(Z)\) indicates that all interventions in \(N_i(G_n)\) are treated.
- \(C_i(Z)\) indicates that all interventions in \(N_i(G_n)\) are control.
- The estimator inverse-probability weights these realized exposure events.
- Hájek normalization divides by the realized weighted exposure totals.
- The first-order linearization is the object whose graph-dependent variance drives inference.

@formal def:hetero-hajek-estimator

---

## The envelope turns unknown outcomes into a design criterion

- The exact linearization variance depends on unknown finite-population outcomes.
- Bounded potential outcomes allow a uniform upper bound.
- The envelope \(V_{\mathrm{env}}(G_n,p)\) depends only on the graph and the candidate probabilities.
- Pairwise shared neighborhoods determine how much inverse-probability weighting amplifies covariance.
- Minimizing this envelope gives an outcome-model-free design rule.

@formal def:graph-envelope

---

## Heterogeneous probabilities preserve the homogeneous benchmark

@informal prop:homogeneous-reduction: When all intervention probabilities are equal, the covariance loads reduce to functions of shared-neighborhood sizes and give the homogeneous Bernoulli variance representation.

- This anchors the paper in the existing homogeneous Bernoulli bipartite framework.
- Shared-neighborhood size is the key graph object even before heterogeneity enters.
- The benchmark clarifies what graph-adaptive probabilities are allowed to improve.

---

## The variance representation separates outcomes from graph loads

@informal thm:hetero-envelope: Under positive assignment probabilities, independent heterogeneous Bernoulli assignment, and bounded all-treated and all-control outcomes, the linearization covariance has graph-and-design loads and its variance scale is at most \(V_{\mathrm{env}}(G_n,p)\).

@formal thm:hetero-envelope

---

## The optimal design is computable from the graph

@informal thm:convex-design: Under \(0<\epsilon<1/2\) and an admissible budget, the feasible class is nonempty, compact, and convex, the graph envelope is convex, and an envelope minimizer satisfies KKT conditions.

@formal thm:convex-design

---

## The central insight is probability moves along overlap gradients

- The score \(g_k(G_n,p)\) measures the envelope's marginal response to changing intervention \(k\)'s probability.
- At an interior optimum, all active coordinates have the same budget-adjusted score.
- At probability bounds, complementary slackness gives the one-sided condition.
- A naive degree-only rule can miss pairwise overlap coupling across shared neighborhoods.
- The envelope score repairs this by aggregating every outcome pair whose exposure dependence runs through intervention \(k\).

---

## The graph-adaptive estimator is asymptotically normal

@informal thm:hetero-clt: Under the stated local-dependence conditions, the Hájek estimator has a normal limit after design-variance scaling.

@formal thm:hetero-clt

---

## A graph-only Wald scale gives conservative coverage

@informal thm:postdesign-wald: Under the same local-dependence and feasibility conditions with a valid two-sided Wald critical value, \(V_{\mathrm{env}}(G_n,p_n)\) upper-bounds the variance scale for every \(n\) and yields asymptotic coverage at least \(1-\alpha_{\mathrm{cov}}\).

@formal thm:postdesign-wald

---

## Heterogeneity can strictly improve the envelope

@informal thm:heterogeneity-separation: With an admissible budget, homogeneous rate \(\rho\) inside the positivity box and \(\rho\neq 1/2\), unequal homogeneous-point envelope scores imply that every envelope optimum differs from homogeneity and improves the envelope by at least the stated directional-curvature bound.

@formal thm:heterogeneity-separation

---

## A separable surrogate has a bounded-degree certificate

- The full envelope couples probabilities across shared neighborhoods.
- The surrogate replaces that coupled objective with an additive weighted sum over intervention units.
- Its weights \(h_k(G_n)\) summarize how intervention \(k\) participates in shared-neighborhood pairs.
- Under bounded outcome degree, this simpler rule stays within an explicit multiplicative envelope certificate.
- In the running example, reporting \(\max_i d_i\), \(\epsilon\), and the certificate says how informative the shortcut is.

@informal thm:surrogate-certificate: Under an admissible floor, bounded outcome degree, and an admissible budget, the separable surrogate is sandwiched by \(V_{\mathrm{env}}(G_n,p)/4\) and its approximation ratio is at most \(\max\{1,\epsilon^{-(\bar d-1)}\}\).

---

## The surrogate certificate uses bounded local neighborhoods

@informal thm:dispersion-certificate-unbounded: For any admissible \(\epsilon\), degree-dispersion constant, and \(h\)-weight ratio constant, there are unbounded-degree graph sequences satisfying those dispersion and weight-ratio conditions whose surrogate approximation ratio diverges.

@informal lem:bounded-degree-dependency-clt: Centered, uniformly bounded summands with bounded dependency-graph degree and linearly growing variance satisfy a normal approximation after standardization.

- The positive certificate is a bounded-outcome-degree statement.
- The CLT uses the same local-dependence logic: exposure summands can depend only through bounded overlap neighborhoods.
- Degree summaries on the intervention side are useful diagnostics, while the envelope itself tracks higher-order shared-neighborhood structure.

---

## The contribution is graph-adaptive design with inference

- The paper characterizes heterogeneous Bernoulli designs for bipartite interference experiments.
- It constructs a graph-only variance envelope for the Hájek linearization.
- It proves convex feasibility, optimality conditions, and strict separation from homogeneous assignment under score heterogeneity.
- It establishes asymptotic normality and conservative Wald coverage under bounded local dependence.
- It gives a bounded-degree approximation certificate for a separable surrogate and explains the graph structure needed for that certificate.
