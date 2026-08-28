# Uniform Expected Risk for Boundary Distance Designs

We characterize how distance compression sets the expected uniform-risk scale for boundary regression discontinuity designs: unsigned distance forces the \((\log n/n)^{1/4}\) lower bound, and signed known-geometry local polynomials match that scale under the stated analytic inputs.

---

## Overview

- The frontier normalization \(a_n\), the benchmark for expected supremum loss, is
\[
a_n=\left(\frac{\log n}{n}\right)^{1/4}.
\]

- Unsigned distance rules observe outcomes and scalar distances from each boundary query point.

- For those rules, expected boundary sup-loss is bounded below on the \(a_n\) scale.

- Signed-distance rules also know the treatment side and boundary geometry.

- Under \(\mathsf{AI}_{p,\nu,L}\), the signed known-geometry minimax risk is characterized up to constants on the same scale.

---

## Motivation

- In a geographic regression discontinuity design, treatment changes at a border: school districts, precincts, jurisdictions, or policy regions.

- Distance to the border is a natural one-dimensional running coordinate.

- For one boundary location, distance looks like the familiar scalar regression discontinuity coordinate.

- For the entire boundary, the same sample is re-expressed at many query points.

- Uniform expected risk asks how accurately a distance-based rule can recover the whole boundary curve.

- The central question is how much uniform accuracy survives the distance reduction.

---

## Distance experiments

@figure distance-experiments: Box-and-arrow schematic comparing a boundary point, nearby observations, unsigned distance, signed distance, side labels, known geometry, and supremum loss.

- Unsigned distance keeps how far an observation is from the query point.

- Signed distance keeps how far and which side of the treatment boundary the observation lies on.

- The unsigned target is the boundary regression function \(\mu_P\), the conditional mean at the support boundary.

- The signed target is \(\tau_P(x)\), the boundary treatment-effect curve.

- Both risks evaluate the expected supremum error along the boundary.

---

## Unsigned setup

- The class \(\mathcal P_{\mathrm{NP}}(L,q)\), the compact bivariate nonparametric law class, has bounded density, Hölder regression, continuous bounded variance, and a Lipschitz support boundary.

- At boundary point \(x\), the rule sees \((Y_i,\lVert X_i-x\rVert_2)\).

- The common-map class uses one law-independent distance rule across all boundary points.

- The point-indexed class permits a separate law-independent distance rule at each query point.

- The loss is expected sup-error for estimating \(\mu_P(x)\) over \(\operatorname{bd}(\mathcal X_P)\).

---

## Signed setup

- The known geometry \(G_P\), the bundled design object, gives the support, assignment regions, interface, Euclidean metric, and uniform kernel.

- Signed distance assigns positive and negative signs using the treatment side.

- The class \(\mathcal P_{12}(p,\nu,L)\), the A1/A2 law class, supplies rectangular support, bounded density, smooth arm regressions, moments, variances, rectifiable interface, local mass, and stable Gram matrices.

- The target \(\tau_P(x)\), the treatment-effect curve, is the arm-specific regression jump at boundary point \(x\).

- In the geographic example, this is the effect curve traced along the policy border.

---

## Key idea

@figure unsigned-hypercube: Box-and-arrow schematic showing separated boundary cells, hidden binary perturbations, unsigned distance observations, supremum loss, the scale calculation, balancing, and decoding difficulty.

- The lower-bound construction plants many separated cells along the boundary.

- Each cell carries a hidden binary perturbation and a boundary signal \(\Delta\).

- Smoothness permits cells with radius at the \(\Delta^{1/q}\) scale and count at the \(\Delta^{-1/q}\) scale.

- Unsigned distances preserve radius and mix angular directions, so each bit carries weak information \(n\Delta^4\).

- Uniform loss forces simultaneous recovery across cells.

- Balancing \(n\Delta^4\) with \(\log M\) yields the \(a_n\) scale.

---

## Main result I

@informal thm:cty-same-class-log-converse: For every \(q\geq1\) and \(L\geq4\), common-map unsigned rules have minimax expected boundary sup-loss at least a constant multiple of \(a_n\).

- This is the Cattaneo et al. (2026) common-map architecture.

- The result keeps the law class, information set, target, decision class, and expected supremum loss fixed.

@formal thm:cty-same-class-log-converse

---

## Main result II

@informal lem:common-map-strict-in-point-indexed: For \(n\geq1\), \(q\geq1\), and \(L\geq4\), point-indexed unsigned rules strictly contain common-map rules.

@informal thm:point-indexed-distance-log-converse: For \(q\geq1\) and \(L\geq4\), point-indexed unsigned rules also have minimax outer-expected boundary sup-loss at least a constant multiple of \(a_n\).

- The rule may use a different law-independent distance rule at each boundary point.

- The lower scale is tied to outcomes plus unsigned scalar distances.

@formal thm:point-indexed-distance-log-converse

---

## Signed lower bound

@informal lem:cty-a1-a2-rectangle-angular-hypercube-all-orders: For each \(p\), the fixed rectangle supports a signed-distance hypercube with exact \(\Delta\) target separation and local KL bounded by the \(\Delta^4/w^2\) scale.

@informal thm:cty-a1-a2-point-indexed-log-converse-all-orders: For every fixed \(p\), \(\nu\geq2\), and \(L\geq L_0(p)\), signed-distance known-geometry rules have minimax outer risk at least a constant multiple of \(a_n\).

- The hard experiment is a fixed treated rectangle inside a fixed square, including corner points.

- Signed-distance rules know the geometry and side labels; the construction carries many weak boundary bits under that information set.

@formal thm:cty-a1-a2-point-indexed-log-converse-all-orders

---

## Analytic inputs

- The signed upper bound is conditional on \(\mathsf{AI}_{p,\nu,L}\), the three assumed signed-distance inputs.

- Identification: one-sided signed-distance conditional means identify \(\tau_P(x)\).

- Approximation: population local-polynomial intercept bias is uniformly first order in bandwidth.

- Stochastic control: expected uniform Gram and raw-score deviations obey the maximal bounds, including the heavy-tail exponent \(n^{(1+\nu)/(2+\nu)}\).

@informal lem:euclidean-balls-vc: Closed Euclidean balls in the plane shatter at most three points in this finite-set certificate.

@informal lem:cty-winsorized-score-maximal-bound: For clipped signed-distance local-polynomial scores, the expected outer supremum is at most the sum of a square-root empirical term and a bounded-envelope term.

---

## Signed upper bound

@informal prop:cty-a1-a2-winsorized-expected-outer-upper: Under the three signed-distance analytic inputs, the stabilized signed-distance local-polynomial estimator has expected outer interface sup-loss at most \(C a_n\) for all sufficiently large \(n\).

- Mechanism: at bandwidth \(h_n=a_n\), winsorize outcomes at \(B_n=a_n^{-1/3}\).

- Fit separate degree-\(p\) signed-distance local polynomials on each side.

- Stabilize the Gram inverse and clip the final jump estimate.

- The bandwidth balances first-order bias with the uniform stochastic scale.

@formal prop:cty-a1-a2-winsorized-expected-outer-upper

---

## Matched frontier

@informal thm:cty-a1-a2-winsorized-matched-frontier: Under \(\mathsf{AI}_{p,\nu,L}\), for every fixed \(p\), \(\nu\geq2\), and \(L\geq L_0\), the signed-distance minimax risk is bounded below and above by constant multiples of \(a_n\).

- The lower inequality comes from the fixed-geometry signed hypercube.

- The upper inequality is attained by the explicit winsorized, Gram-stabilized degree-\(p\) estimator.

- In the geographic example, known side labels and boundary geometry support a two-sided risk characterization for the treatment-effect curve.

@formal thm:cty-a1-a2-winsorized-matched-frontier

---

## Lower-bound mechanics

@informal lem:coordinatewise-overlap-direct-product: If each compressed coordinate has KL at most a fixed fraction of \(\log M\), the probability of at least one binary decoding error is at least the stated overlap lower bound.

@informal lem:cty-support-boundary-angular-packing: For \(q\geq1\) and \(L\geq4\), the support-boundary construction supplies separated cells with signal separation at least \(c_1a_n\) and compressed-distance KL at most \(\alpha\log M_n\).

- A rule with small uniform error would decode every hidden bit.

- The direct-product step converts weak per-cell information into a high probability of at least one decoding error.

- One decoding error forces supremum loss at the boundary signal scale.

---

## Upper-bound mechanics

- Identification turns the signed-distance conditional mean jump into the treatment-effect target.

- The population local polynomial tracks that jump to first order in the bandwidth.

- The empirical Gram condition keeps the two side-specific fits stable.

- Winsorization converts the moment envelope into a bounded-score empirical process.

- The expected maximal bounds control the supremum over arms, interface points, and laws.

---

## Background

- Classical regression discontinuity starts with threshold designs: Thistlethwaite and Campbell (1960) and Hahn et al. (2001).

- Modern RD inference emphasizes local polynomial estimation, bandwidths, and robust correction: Imbens and Lemieux (2008), Lee and Lemieux (2010), Fan and Gijbels (1996), Calonico et al. (2014), and Calonico et al. (2020).

- Boundary and geographic RD motivate vector scores and interface-indexed targets: Keele and Titiunik (2015), Keele et al. (2015), Keele and Titiunik (2016), and Cattaneo et al. (2026).

- Our contribution uses the minimax and empirical-process vocabulary of Stone (1982), Tsybakov (2009), Vapnik and Chervonenkis (1971), Pollard (1984), and van der Vaart and Wellner (1996).

---

## Open questions

- We establish unconditional logarithmic lower bounds for unsigned common-map and point-indexed distance rules over \(\mathcal P_{\mathrm{NP}}(L,q)\).

- We establish an unconditional signed-distance lower bound on a fixed rectangular subexperiment.

- Under \(\mathsf{AI}_{p,\nu,L}\), we obtain the signed known-geometry two-sided expected outer-risk frontier.

- The shared \(a_n\) scale compares delivered lower scales; the signed two-sided frontier is the conditional characterization.

- Open directions: a matching unsigned upper bound, a self-contained derivation of the signed analytic inputs on the displayed law class, and extensions to non-Euclidean metrics, kernels, and geometry envelopes.
