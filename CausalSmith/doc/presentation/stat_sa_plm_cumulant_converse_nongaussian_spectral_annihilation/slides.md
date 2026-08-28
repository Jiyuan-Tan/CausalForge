# Contour Instruments for Learned Treatment Residuals

A zero of the treatment-noise transform turns residualized treatment into a stable instrument, giving fixed-code minimax mean-squared error of order \(n^{-1}\) under fixed cumulant separation.

---

## The paper establishes a root-\(n\) contour route to \(\theta_0\)

- Target: \(\theta_0\), the partially linear coefficient on residualized treatment.
- Data: \(O=(X,T,Y)\), with supplied treatment and outcome codes \(\bar g_n,\bar q_n\).
- Signal: the treatment innovation \(\eta=T-g_0(X)\) is independent of \(X\), sub-Gaussian, and has a fixed nonzero cumulant.
- Device: zeros of \(M(z)=E[e^{z\eta}]\), the treatment-innovation moment-generating function.
- Payoff: a finite contour statistic attains fixed-code minimax MSE between \(c/n\) and \(C/n\).
- The result gives an affirmative fixed-separation benchmark for learned-residual partially linear estimation.

@informal thm:adaptive-rootn-minimax: Under fixed primitive constants and the theorem's fixed-code gates, the contour statistic has minimax MSE between \(c/n\) and \(C/n\).

---

## Learned treatment residuals create a concrete nuisance problem

- Classical residualization estimates \(\theta_0\) from treatment variation after removing \(g_0(X)\).
- In the paper’s finite-\(n\) experiment, the analyst supplies a deterministic code \(\bar g_n\).
- The working residual is \(Z_n=T-\bar g_n(X)\).
- The treatment-code error is \(D_n(X)=g_0(X)-\bar g_n(X)\).
- A running example: a flexible ML treatment model is trained elsewhere, then treated as the fixed code for the conference-sample analysis.
- The question is: what extra identifying information is carried by non-Gaussian residual treatment variation?

---

## The key model restrictions have direct empirical meaning

- \(\eta=T-g_0(X)\) is independent of \(X\): treatment noise is separated from covariates after the treatment regression.
- \(E[\xi\mid X,T]=0\): the partially linear conditional mean is correctly centered.
- \(|\theta_0|\le C_\theta\), \(\|g_0\|_\infty\le C_g\), and \(\|q_0\|_\infty\le C_q\): the target and regressions live on fixed ranges.
- \(\eta\) and \(\xi\) satisfy the stated sub-Gaussian envelopes.
- \(|\kappa_k(\eta)|\ge\delta\): the \(k\)th cumulant is separated from zero by a fixed amount.
- In the running example, the supplied treatment code must be accurate in \(L^1(P_X)\) at the displayed current radius.

---

## A transform zero becomes an instrument

- Suppose \(z_0\) is a zero of \(M(z)=E[e^{z\eta}]\), with multiplicity \(\ell\).
- The zero-based instrument is a polynomial-exponential weight applied to the residual.
- The crucial shift property: the same zero moment survives real shifts from treatment-code error.
- Conditioning on \(X\) turns that shift property into a valid moment for \(Z_n=T-\bar g_n(X)\).
- When the denominator is nonzero, the ratio identifies \(\theta_0\).

@formal thm:known-zero-instrument

---

## Contours average over the unknown zeros

- A known zero gives a direct ratio; an unknown zero calls for a search rule.
- The observable treatment-residual transform \(F_n\) carries the zero locations.
- The observable outcome-weighted transform \(G_n\) carries the numerator information.
- A contour circle counts enclosed zeros and averages \(G_n/F_n\) around the boundary.
- The contour is valid when the residual transform is zero-free on the boundary, the nuisance factor is zero-free inside, and at least one zero is enclosed.

@figure contour-identification: Box-and-arrow schematic showing supplied code and data forming residual \(Z_n\), residual transform \(F_n\) and outcome transform \(G_n\), a selected contour with enclosed zeros, and the resulting estimate of \(\theta_0\).

@formal thm:exact-contour-identification

---

## Cumulant separation gives a finite search region

- The paper uses the fixed nonzero cumulant as a quantitative non-Gaussian signal.
- Sub-Gaussian control keeps the transform well behaved on complex disks.
- Cumulant separation places at least one zero of \(M\) inside the explicit radius \(R_0\).
- The contour bank searches between \(R_0\) and \(R_1=R_0+1\).
- The finite bank is chosen once from the primitive constants.

---

## \(L^1(P_X)\) treatment-code stability preserves zero geometry

- The nuisance factor is \(H_n(z)=E[e^{zD_n(X)}]\).
- The \(L^1(P_X)\) treatment-code radius controls how far \(H_n\) moves from one.
- Under the displayed small-radius gate, \(H_n\) stays bounded away from zero on the search disk.
- Then \(F_n(z)=M(z)H_n(z)\) has the same zero geometry as \(M\) inside the search region.
- In the running example, this is exactly where the trained treatment code enters the contour theorem.

---

## The estimator is a split-sample contour program

- Mechanism: form \(Z_{n,i}=T_i-\bar g_n(X_i)\).
- Pilot fold: compute empirical transforms and choose a bank circle with certified boundary separation and positive winding count.
- Evaluation fold: compute the normalized contour average of \(\widehat G/\widehat F\) on the selected circle.
- Output: take the real midpoint of the certified contour interval and clip it to \([-C_\theta,C_\theta]\).
- The represented-data layer realizes the same ordinary Borel statistic when the bounded spectral adapter satisfies its build-and-compilation specification.

@figure estimator-pipeline: Box-and-arrow schematic showing observations and supplied treatment code, residual construction, pilot-fold contour selection, evaluation-fold contour ratio, clipping, and output \(\widehat\theta_{\mathrm{spec},n}\).

---

## The fixed-separation theorem is the main statistical result

@formal thm:adaptive-rootn-minimax

---

## The same bank works across fixed-constant sequences

- Along sequences sharing the fixed primitive constants, the transported primitive records generate the same contour bank.
- The contour statistic remains measurable and keeps the \(c/n\) to \(C/n\) fixed-code non-Gaussian MSE bounds.
- On the bounded-outcome Gaussian JMS comparison class, the target degenerates to zero and the fixed-code Gaussian risks are zero.
- This separates the fixed non-Gaussian contour experiment from the bounded Gaussian diagnostic.

@informal thm:common-experiment-dichotomy: Along fixed-constant non-Gaussian sequences satisfying the displayed code gate, the contour bank gives minimax MSE between \(c/n_j\) and \(C/n_j\); on the bounded-outcome Gaussian JMS class, \(\theta_0(P)=0\) and the fixed-code Gaussian risks are zero.

@informal prop:bounded-outcome-gaussian-degeneracy: In the bounded-outcome Gaussian JMS class, every model has \(\theta_0(P)=0\), and any nonempty fixed-code intersection has zero Gaussian MSE and generalized-quantile minimax risks.

---

## The ACE comparison aligns the common class

- JMS ACE uses order \(r\) and \(L^r(P_X)\) treatment and outcome code radii.
- The contour theorem uses the current \(L^1(P_X)\) treatment-code gate to preserve transform zeros.
- On bounded ranges, the ACE treatment-radius condition supplies the needed \(L^1(P_X)\) control.
- When \(s=r\), the common clipped-code class matches the ACE-restricted spectral subclass.
- Under JMS eligibility, both published ACE and contour upper guarantees can be read on the same class.

@formal prop:jms-ace-alignment

---

## The proof is a three-step stability story

- Step 1: cumulant separation and the sub-Gaussian envelope force a transform zero inside the fixed search disk.
- Step 2: the treatment-code error changes the residual transform only through \(H_n\), and the \(L^1(P_X)\) gate keeps that factor away from zero.
- Step 3: uniform empirical transform control makes the selected empirical contour close to a valid population contour.
- The lower bound comes from a one-dimensional fixed-code submodel with local shifts of \(\theta_0\) and controlled product relative entropy.
- Together these give the matched \(n^{-1}\) MSE scale.

---

## Mixture examples make the mechanism explicit

- In the symmetric Gaussian mixture benchmark, the transform zero is known at \(i\pi/2\).
- The contour ratio collapses to a clipped sine ratio using \(Y\sin(\pi Z_n/2)\) and \(Z_n\sin(\pi Z_n/2)\).
- Under the stated \(L^1(P_X)\) treatment-code condition, the denominator stays bounded away from zero.
- The estimator attains MSE at most \(C/n\) in that benchmark.

@informal prop:symmetric-mixture-reduction: For the symmetric mixture \(\tfrac12N(-1,1)+\tfrac12N(1,1)\), the clipped sine-ratio estimator has mean-squared error at most \(C/n\) under the stated independence, range, tail, sampling, and treatment-code conditions.

---

## Local benchmarks track weakening non-Gaussianity

- The Gaussian--Rademacher path gives an explicit fourth-cumulant parameter \(\Delta_a=2a^4\).
- Its first positive transform zero, denominator scale, and sine estimator are all computable from \(a\).
- The local ACE oracle envelope records the published ACE upper bound with shrinking cumulant threshold \(\delta_n\).
- These benchmarks organize the triangular-array regime where non-Gaussian signal weakens with \(n\).

@informal thm:local-to-gaussian-partial-benchmarks: Along the Gaussian--Rademacher path, the sine estimator obeys the stated explicit MSE upper bound, and under the published ACE handle hypotheses the local ACE estimator obeys the displayed generalized-quantile upper envelope with \(\Delta=\delta_n\).

---

## The contribution is a fixed-separation contour benchmark

- The paper constructs zero-based instruments for learned treatment residuals in partially linear models.
- It turns unknown transform zeros into an observable contour ratio for \(\theta_0\).
- It gives a finite, fixed-code contour statistic with matched \(c/n\) and \(C/n\) MSE bounds under fixed cumulant separation.
- It aligns that guarantee with the published order-\(r\) ACE comparison on the common clipped-code class.
- It supplies explicit sine-ratio benchmarks for mixture treatment innovations and a local benchmark agenda for shrinking cumulant separation.
