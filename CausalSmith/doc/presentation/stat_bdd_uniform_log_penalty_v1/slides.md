# Uniform Risk from Distance Compression

Distance-only boundary rules incur expected sup-loss on the \(a_n=(\log n/n)^{1/4}\) scale; signed-distance local polynomials attain the same scale under the stated analytic inputs.

---

## The paper characterizes a boundary risk frontier

- Boundary RD asks for a curve of causal or regression quantities, not one cutoff value.
- The loss is uniform: the rule is judged by its worst error along the boundary.
- The paper studies what happens when two-dimensional location is compressed to distance from each query point.
- In the unsigned experiment, distance compression creates a logarithmic minimax lower bound.
- In the signed known-geometry experiment, the same scale is matched by a stabilized local-polynomial estimator conditional on \(\mathsf{AI}_{p,\nu,L}\).

@informal thm:cty-a1-a2-winsorized-matched-frontier: Under the stated signed-distance analytic inputs and envelope threshold, the signed-distance minimax outer risk is bounded above and below by constant multiples of \(a_n\).

---

## Distance is useful precisely because it throws information away

- In geographic RD, distance to a boundary is a natural running variable.
- But distance from a query point forgets angular location around that point.
- Unsigned distance also forgets which treatment side generated an observation.
- The statistical question is: what is the cost of using that compressed experiment for a whole boundary curve?
- The answer is a uniform testing penalty on the \(a_n=(\log n/n)^{1/4}\) scale.

@figure distance-compression: A box labeled bivariate observations points to a box labeled unsigned distances from query point and outcomes, which points to a box labeled boundary regression estimate.

---

## The running example is a geographic boundary design

- Think of a policy assigned on one side of a known municipal border.
- Near any border point, local comparisons use observations close to that point.
- With signed distance, an observation carries distance and policy side.
- With unsigned distance, an observation carries distance but loses side and angle.
- The paper separates these two information sets and evaluates uniform expected boundary error.

---

## The unsigned experiment targets a regression boundary

- The law class \(\mathcal P_{\mathrm{NP}}(L,q)\) contains compact bivariate random-design regressions.
- The regression function \(\mu_P\), the conditional mean, is \(q\)-smooth on the support.
- The design density and conditional variance are uniformly bounded above and below.
- At boundary point \(x\), the rule observes \(V_{n,P}(x)\): outcomes and Euclidean distances from \(x\).
- The risk is expected sup-loss over the support boundary.

@formal def:cty-nonparametric-class

---

## Two unsigned rule classes face the same barrier

- A common-map rule uses one law-independent map at every boundary point.
- A point-indexed rule may choose a separate law-independent Borel section for each \(x\).
- Point-indexing gives more procedural flexibility while preserving the same unsigned distance data.
- Outer expectation handles the boundary supremum for the point-indexed class.
- The lower bound survives this larger decision class.

@formal def:cty-distance-data

---

## The unsigned common-map risk has logarithmic lower scale

@informal thm:cty-same-class-log-converse: For every \(q\geq1\) and \(L\geq4\), the common-map minimax expected boundary sup-loss is at least a constant multiple of \(a_n\) asymptotically.

@formal thm:cty-same-class-log-converse

---

## The unsigned point-indexed risk has the same lower scale

@informal thm:point-indexed-distance-log-converse: For every \(q\geq1\) and \(L\geq4\), even point-indexed unsigned distance rules have outer-expected boundary sup-loss at least a constant multiple of \(a_n\) asymptotically.

@formal thm:point-indexed-distance-log-converse

---

## The lower-bound construction hides many local bits

- Place many separated perturbation cells along the support boundary.
- Each cell changes the boundary regression value by order \(a_n\).
- The unsigned distance distribution at the queried boundary point is calibrated to reveal little about the local bit.
- The number of cells contributes the logarithm through uniform sup-loss.
- The scale calculation is \(M\asymp\Delta^{-1/q}\), \(w^2\asymp\Delta^{2/q}\), and compressed information \(n\Delta^4\).
- Balancing \(n\Delta^4\asymp\log M\) gives \(\Delta\asymp(\log n/n)^{1/4}\).

@figure unsigned-hypercube: A row of labeled boundary cells points to a box labeled hidden binary perturbations, which points to a box labeled scalar distance observations, which points to a box labeled decoding difficulty.

---

## Signed distance adds the geometry needed for local RD fitting

- The signed experiment targets \(\tau_P(x)\), the treatment-effect curve along the known interface.
- The rule knows the support, assignment regions, interface, Euclidean metric, and uniform kernel.
- The signed distance is positive on the treated side and negative on the control side.
- In the running geographic example, this means the border and policy side are part of the design information.
- Local-polynomial fitting uses signed distance as a one-dimensional coordinate.

@formal def:cty-known-geometry-signed-distance-data

---

## The signed law class fixes smoothness, moments, and local conditioning

- \(\mathcal P_{12}(p,\nu,L)\) is the displayed Euclidean, uniform-kernel CTY-style boundary class.
- Potential-outcome regressions have \(C^{p+1}\) extensions.
- Conditional variances and \(2+\nu\) moments are uniformly controlled.
- The interface is a compact rectifiable curve of controlled length.
- The Gram and arm-mass clauses keep local polynomial fits stable at every interface point.

@formal def:cty-a1-a2-class

---

## The signed lower bound already holds on a fixed rectangle

@informal thm:cty-a1-a2-point-indexed-log-converse-all-orders: For every polynomial order \(p\), above the envelope threshold \(L_0(p)\), the signed-distance minimax outer risk is at least a constant multiple of \(a_n\), even on the fixed hard geometry.

@formal thm:cty-a1-a2-point-indexed-log-converse-all-orders

---

## The estimator is stabilized local polynomial smoothing

- Split observations by signed side of the boundary.
- Within bandwidth \(h\), fit a degree-\(p\) polynomial in signed distance on each side.
- Winsorize outcomes at \(B(h)=h^{-1/3}\) to control heavy tails.
- Invert the empirical Gram matrix only when it is uniformly well conditioned.
- Clip the final intercept difference to the envelope range.

@formal def:cty-stabilized-local-polynomial-estimator

---

## The signed upper bound uses three analytic inputs

- \(\mathsf{AI}_{p,\nu,L}\) collects distance identification, first-order bias control, and expected maximal bounds.
- These three inputs are assumptions for the signed upper theorem.
- The winsorized-score lemma supplies the bounded-envelope score component.
- The upper result also uses the assumed uniform Gram control and the assumed raw-score heavy-tail maximal bound.
- With bandwidth \(h_n=a_n\), first-order bias and uniform stochastic fluctuation balance at the same scale.

@formal synth_139

---

## The stabilized estimator attains the conditional upper rate

@informal prop:cty-a1-a2-winsorized-expected-outer-upper: Under the displayed signed-distance analytic inputs, the stabilized signed-distance local-polynomial estimator has expected outer sup-loss at most a constant multiple of \(a_n\).

@formal prop:cty-a1-a2-winsorized-expected-outer-upper

---

## The conditional signed frontier matches lower and upper bounds

@informal thm:cty-a1-a2-winsorized-matched-frontier: Under the stated analytic inputs, the signed-distance known-geometry minimax risk is characterized up to constants on the \(a_n\) scale.

@formal thm:cty-a1-a2-winsorized-matched-frontier

---

## The proof reduces uniform estimation to many hard tests

- A direct-product inequality converts many weakly distinguishable coordinates into a high probability of at least one error.
- The unsigned packing makes scalar distances nearly invariant to the bit that changes the boundary value.
- The signed rectangle hypercube repeats the testing logic inside one known geometry.
- The upper proof decomposes signed-distance estimation error into bias, Gram stability, and score fluctuation.
- The rate emerges when the local-polynomial bandwidth is set to the same scale as the boundary testing amplitude.

---

## The contribution is a precise risk map for distance-based boundary RD

- Over \(\mathcal P_{\mathrm{NP}}(L,q)\), unsigned distance rules have minimax expected boundary sup-loss bounded below on the \(a_n\) scale.
- The lower bound applies to both CTY common-map rules and the larger point-indexed Borel class.
- Over \(\mathcal P_{12}(p,\nu,L)\), signed-distance known-geometry rules have an unconditional fixed-geometry lower bound.
- Under \(\mathsf{AI}_{p,\nu,L}\), the stabilized signed-distance local-polynomial estimator attains the matching outer-expected upper scale.
- The paper explains exactly how distance compression, boundary uniformity, and known treatment geometry determine the attainable risk.
