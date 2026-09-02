# Distance Is Data, and Data Have Limits

TL;DR: Distance-based boundary RD designs face expected sup-loss at least of order \(a_n=(\log n/n)^{1/4}\); signed-distance local polynomials match that scale under the paper’s stated analytic inputs.

---

## Punchline

- The paper studies what is statistically recoverable when boundary data are compressed to distances.
- In the unsigned experiment, a rule sees \((Y_i,\|X_i-x\|_2)\) at each boundary query point \(x\).
- The paper proves an unconditional logarithmic minimax lower bound over \(\mathcal P_{\mathrm{NP}}(L,q)\).
- The bound holds even for point-indexed Borel rules, which may choose a different law-independent section at each \(x\).
- In the signed known-geometry experiment, a stabilized local-polynomial estimator reaches the same \(a_n\) scale under \(\mathsf{AI}_{p,\nu,L}\): three CTY-style analytic inputs assumed here, not proved (spelled out later).
- The destination: distance compression creates a uniform boundary-testing cost.

---

## Why This Matters

- Boundary RD designs arise when treatment changes across a geographic or policy frontier.
- Running example: households near a school-district boundary, with achievement as \(Y\) and assigned district as treatment.
- Applied work often reduces two-dimensional location to distance from the border.
- That reduction can be useful, but it changes the statistical experiment.
- The question here is sharp: what uniform boundary risk follows from the distance information actually given to the rule?

---

## Two Distance Experiments

- Unsigned distance: the rule sees how far each observation is from \(x\), but not which direction or side it came from.
- Signed distance: the rule sees distance with a sign determined by the known treatment side.
- In the school-boundary example, unsigned distance forgets which district side a student lies on.
- Signed distance keeps the side label and uses the known border geometry.
- The paper analyzes both experiments under expected supremum loss over the boundary.

@figure distance-experiments: A boundary point x on a treatment interface, with nearby observations collapsed either to unsigned radial distances or to signed distances by treatment side.

---

## Setup: Unsigned Boundary Regression

- The target is the boundary regression curve \(x\mapsto\mu_P(x)\).
- The law class \(\mathcal P_{\mathrm{NP}}(L,q)\) has compact bivariate support, bounded density, Hölder regression smoothness, and nondegenerate variance.
- The frontier rate is \(a_n=(\log n/n)^{1/4}\), the normalization against which every risk statement here is measured.
- A common-map rule applies one law-independent map to \(V_{n,P}(x)\) at every boundary point.
- A point-indexed rule may choose a law-independent Borel section separately for each \(x\).
- Both risks measure expected sup-loss along \(\operatorname{bd}(\mathcal X_P)\).

---

## Setup: Signed Known-Geometry RD

- The target is the treatment-effect curve \(\tau_P(x)\), the jump between arm-specific regression surfaces at the boundary point.
- The known geometry \(G_P\) gives the support, assignment regions, common interface, Euclidean metric, and uniform kernel.
- The signed-distance sample \(U^{\pm}_{n,P}(x)\) records outcomes and signed distances from \(x\).
- The class \(\mathcal P_{12}(p,\nu,L)\) imposes smooth potential-outcome regressions, bounded density and variance, \(2+\nu\) moments, stable two-sided local mass, and stable Gram matrices.
- In the school-boundary example, these assumptions say both sides of the border have enough nearby observations for uniformly stable local fits.

---

## The Estimator in One Sentence

- The signed upper bound uses degree-\(p\) local polynomials on signed distance.
- Mechanism: fit each arm locally within bandwidth \(h\), use the uniform kernel, winsorize outcomes at \(B(h)=h^{-1/3}\), invert the empirical Gram matrix only when it is stable, and clip the final contrast.
- The bandwidth used for the theorem is \(h_n=a_n\).
- The design balances first-order bias of order \(h_n\) against uniform stochastic fluctuation of order \(\{\log(h_n^{-1})/(n h_n^2)\}^{1/2}\).
- At \(h_n=a_n\), both terms sit on the \(a_n\) scale.

---

## Key Idea

- The hard part is uniform recovery over many boundary locations at once.
- The construction puts many separated binary perturbations along the boundary.
- At each active location, the two possible regression values differ by order \(a_n\).
- Unsigned distance preserves radial information but washes out angular information.
- A rule must decode many weakly distinguishable local bits from compressed observations.
- That many-coordinate testing problem is where the logarithm enters.

@figure boundary-hypercube: A square support with many separated boundary cells, each carrying one binary perturbation whose radial distance distribution is matched at its query point.

---

## Where the Literature Stands

- Classical RD identifies treatment effects at scalar cutoffs and motivates local comparisons.
- Geographic and boundary RD extend this logic to spatial assignment regions and interface-indexed estimands.
- CTY develop distance-based identification and local-polynomial tools for boundary designs.
- CTY’s unsigned common-map lower result gives an \(n^{-1/4}\) lower scale and conjectures the logarithmic strengthening.
- This paper proves the logarithmic unsigned converse on the same law class and information set.
- Conditional on three CTY-style analytic inputs, it also assembles a signed-distance expected-risk frontier.

---

## Main Result: Unsigned Common-Map Converse

@informal thm:cty-same-class-log-converse: For every \(q\geq1\) and \(L\geq4\), common-map unsigned distance rules have minimax expected boundary sup-loss at least a constant multiple of \(a_n\) asymptotically.

@formal thm:cty-same-class-log-converse

---

## Main Result: Point-Indexed Unsigned Converse

@informal thm:point-indexed-distance-log-converse: For every \(q\geq1\) and \(L\geq4\), point-indexed unsigned distance rules have minimax outer-expected boundary sup-loss at least a constant multiple of \(a_n\) asymptotically.

@formal thm:point-indexed-distance-log-converse

---

## Novelty of the Unsigned Lower Bound

- The point-indexed class is larger because each boundary point can use its own Borel section.
- The same lower scale survives that extra flexibility.
- Heuristic calibration: \(M\asymp\Delta^{-1/q}\), \(w^2\asymp\Delta^{2/q}\), and compressed per-coordinate information is \(n\Delta^4\).
- Setting \(n\Delta^4\asymp\log M\) gives \(\Delta\asymp(\log n/n)^{1/4}\).
- Smoothness \(q\) changes constants and cell calibration; the exponent comes from distance compression.

---

## Main Result: Signed-Distance Lower Bound

@informal thm:cty-a1-a2-point-indexed-log-converse-all-orders: For every polynomial order \(p\), sufficiently large envelope \(L\), and \(\nu\geq2\), signed known-geometry point-indexed rules have minimax outer risk at least a constant multiple of \(a_n\), already on a fixed rectangular subexperiment.

@formal thm:cty-a1-a2-point-indexed-log-converse-all-orders

---

## Upper Bound Inputs

- The signed upper result is conditional on \(\mathsf{AI}_{p,\nu,L}\).
- Input 1: distance identification links one-sided signed-distance conditional means to \(\tau_P(x)\).
- Input 2: uniform first-order bias control bounds the population local-polynomial approximation.
- Input 3: expected maximal bounds control Gram deviations and raw-score deviations uniformly over arms, boundary points, and laws.
- The paper’s winsorized-score lemma supplies the bounded-envelope score component.
- The upper proposition uses the full input collection, including uniform Gram control and the raw-score heavy-tail bound with exponent \(n^{(1+\nu)/(2+\nu)}\).

---

## Main Result: Signed-Distance Upper Bound

@informal prop:cty-a1-a2-winsorized-expected-outer-upper: Under the three stated analytic inputs, the winsorized Gram-stabilized signed-distance local-polynomial estimator with \(h_n=a_n\) has uniform expected outer risk at most a constant multiple of \(a_n\).

@formal prop:cty-a1-a2-winsorized-expected-outer-upper

---

## Main Result: Matched Signed Frontier

@informal thm:cty-a1-a2-winsorized-matched-frontier: Under the stated analytic inputs, the signed known-geometry minimax outer risk is characterized up to constants on the \(a_n\) scale, and the explicit stabilized local-polynomial estimator attains the upper side.

@formal thm:cty-a1-a2-winsorized-matched-frontier

---

## Why the Arguments Work

- Lower bounds: start with many separated boundary cells, each carrying one binary signal.
- Calibrate the perturbations so each signal changes the boundary target by the chosen amplitude.
- Match the distance marginal at the queried point so the compressed data reveal little about the local bit.
- Convert estimation accuracy into simultaneous decoding, so one decoding error becomes expected sup-loss on the boundary.
- Signed upper bound: identification turns signed distance into one-sided regression at zero on each side.
- Local-polynomial smoothing, stable Gram matrices, winsorization, and maximal inputs control the expected boundary supremum at \(h_n=a_n\).

---

## Takeaways

- Unsigned scalar distance creates a boundary-uniform information barrier over \(\mathcal P_{\mathrm{NP}}(L,q)\).
- The barrier holds for both common-map and point-indexed unsigned rules.
- Signed distance with known geometry targets the boundary treatment-effect curve under \(\mathcal P_{12}(p,\nu,L)\).
- The fixed rectangular signed experiment already carries the \(a_n\) lower scale.
- Under \(\mathsf{AI}_{p,\nu,L}\), the stabilized signed-distance local-polynomial estimator attains the matching expected outer-risk scale.
- The paper’s contribution is a precise minimax account of how distance compression shapes boundary RD risk.
